mod translator;
mod utils;

use cranelift::prelude::{
    codegen, settings, AbiParam, EntityRef, FunctionBuilder, FunctionBuilderContext, InstBuilder,
    Variable,
};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{DataContext, Linkage, Module, ModuleError};
use std::slice;

use crate::analyzer::value::BUILT_INS;
use crate::analyzer::{value::ValueType, Analyzed, AnalyzedTree};

use translator::FunctionTranslator;

pub struct JIT<'a> {
    builder_context: FunctionBuilderContext,
    ctx: codegen::Context,
    data_ctx: DataContext,
    module: JITModule,
    source: &'a str,
}

impl<'a> JIT<'a> {
    pub fn new(source: &'a str) -> Self {
        let builder = JITBuilder::new(cranelift_module::default_libcall_names());

        let module = JITModule::new(builder.unwrap());
        Self {
            builder_context: FunctionBuilderContext::new(),
            ctx: module.make_context(),
            data_ctx: DataContext::new(),
            module,
            source,
        }
    }

    pub fn compile(&mut self, analyzed: Analyzed) -> Result<fn() -> i64, ModuleError> {
        self.translate(analyzed)?;
        println!("{}", self.ctx.func);

        let id =
            self.module
                .declare_function("::main", Linkage::Export, &self.ctx.func.signature)?;

        let flags = settings::Flags::new(settings::builder());
        cranelift::codegen::verifier::verify_function(&self.ctx.func, &flags).unwrap();

        self.module.define_function(id, &mut self.ctx)?;

        self.module.clear_context(&mut self.ctx);
        self.module.finalize_definitions()?;

        let code = self.module.get_finalized_function(id);

        Ok(unsafe { std::mem::transmute(code) })
    }

    pub fn create_data(&mut self, name: &str, contents: Vec<u8>) -> Result<&[u8], String> {
        self.data_ctx.define(contents.into_boxed_slice());
        let id = self
            .module
            .declare_data(name, Linkage::Export, true, false)
            .map_err(|e| e.to_string())?;

        self.module
            .define_data(id, &self.data_ctx)
            .map_err(|e| e.to_string())?;
        self.data_ctx.clear();
        self.module
            .finalize_definitions()
            .map_err(|e| e.to_string())?;
        let buffer = self.module.get_finalized_data(id);
        Ok(unsafe { slice::from_raw_parts(buffer.0, buffer.1) })
    }

    fn translate(&mut self, analyzed: Analyzed) -> Result<(), ModuleError> {
        let int = self.module.target_config().pointer_type();
        self.ctx.func.signature.returns.push(AbiParam::new(int));

        let mut builder = FunctionBuilder::new(&mut self.ctx.func, &mut self.builder_context);
        let entry_block = builder.create_block();
        builder.append_block_params_for_function_params(entry_block);
        builder.switch_to_block(entry_block);
        builder.seal_block(entry_block);

        let Analyzed {
            tree,
            memory,
            mut lookup,
        } = analyzed;

        let mut variables = memory
            .into_iter()
            .enumerate()
            .map(|(i, _)| Variable::new(i))
            .map(|v| {
                builder.declare_var(v, int);
                v
            })
            .collect::<Vec<_>>();

        for (name, f) in BUILT_INS.iter() {
            let mut sig = self.module.make_signature();
            for arg in &f.args {
                let t = match arg {
                    ValueType::Number | ValueType::Pointer(_) => int,
                    _ => todo!(),
                };
                sig.params.push(AbiParam::new(t));
            }
            if let Some(ret) = &f.ret {
                let t = match ret {
                    ValueType::Number | ValueType::Pointer(_) => int,
                    _ => todo!(),
                };
                sig.returns.push(AbiParam::new(t));
            }

            let callee = self
                .module
                .declare_function(name, cranelift_module::Linkage::Import, &sig)
                .unwrap();

            let local_callee = self.module.declare_func_in_func(callee, builder.func);

            let val = builder.ins().func_addr(int, local_callee);
            let var = Variable::new(variables.len());
            builder.declare_var(var, int);
            builder.def_var(var, val);
            lookup[0]
                .entry(name)
                .or_insert((Vec::new(), 1))
                .0
                .push(variables.len());
            variables.push(var);
        }

        let mut return_var = builder.ins().iconst(int, 0);

        let mut trans = FunctionTranslator {
            source: self.source,
            int,
            builder,
            lookup,
            variables,
            current_scope: 0,
        };

        let root = tree.node(AnalyzedTree::ROOT);
        for &child in root.children() {
            return_var = trans.translate_node(&tree, tree.node(child));
        }

        trans.builder.ins().return_(&[return_var]);
        trans.builder.finalize();
        Ok(())
    }
}
