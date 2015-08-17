#include "core/core.h"
#include "cpu/ir/ir_builder.h"
#include "cpu/ir/passes/pass_runner.h"
#include "emu/profiler.h"

using namespace dreavm::cpu::ir;
using namespace dreavm::cpu::ir::passes;

PassRunner::PassRunner() {}

void PassRunner::AddPass(std::unique_ptr<Pass> pass) {
  passes_.push_back(std::move(pass));
}

void PassRunner::Run(IRBuilder &builder) {
  PROFILER_RUNTIME("PassRunner::Run");

  for (auto &pass : passes_) {
    pass->Run(builder);
  }
}