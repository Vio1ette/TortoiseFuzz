/*
   american fuzzy lop - LLVM-mode instrumentation pass
   ---------------------------------------------------

   Written by Laszlo Szekeres <lszekeres@google.com> and
              Michal Zalewski <lcamtuf@google.com>

   LLVM integration design comes from Laszlo Szekeres. C bits copied-and-pasted
   from afl-as.c are Michal's fault.

   Copyright 2015, 2016 Google Inc. All rights reserved.

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at:

     http://www.apache.org/licenses/LICENSE-2.0

   This library is plugged into LLVM when invoking clang through afl-clang-fast.
   It tells the compiler to add code roughly equivalent to the bits discussed
   in ../afl-as.h.

 */

#define AFL_LLVM_PASS

#include "../../config.h"
#include "../../debug.h"

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

#include "llvm/ADT/Statistic.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/Debug.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"

#include "llvm/Support/raw_ostream.h"

using namespace llvm;

namespace {

  class AFLCoverage : public ModulePass {

    public:

      static char ID;
      AFLCoverage() : ModulePass(ID) { }

      bool runOnModule(Module &M) override;

      // StringRef getPassName() const override {
      //  return "American Fuzzy Lop Instrumentation";
      // }

  };

}

char AFLCoverage::ID = 0; //初始化PassID，LLVM使用ID的地址来标识Pass，所以ID的值并不重要

bool AFLCoverage::runOnModule(Module &M) {

  LLVMContext &C = M.getContext(); //context，存储管理全局数据
  //getContext返回一个类引用，用一个类引用接，没问题啊

  //语法是语法，逻辑是逻辑，学语法的时候专心学语法，看逻辑的时候主要看逻辑，就别纠结于语法细节

  IntegerType *Int8Ty  = IntegerType::getInt8Ty(C); //搞了半天，这是创建一个新的整数啊，创建一个8位宽的整数
  IntegerType *Int32Ty = IntegerType::getInt32Ty(C);//创建一个32位宽的整数

  /* Show a banner */ //一个口号

  char be_quiet = 0;

  if (isatty(2) && !getenv("AFL_QUIET")) {

    SAYF(cCYA "afl-llvm-pass " cBRI VERSION cRST " by <lszekeres@google.com>\n");

  } else be_quiet = 1;

  /* Decide instrumentation ratio */

  char* inst_ratio_str = getenv("AFL_INST_RATIO");
  unsigned int inst_ratio = 100;

  if (inst_ratio_str) {

    if (sscanf(inst_ratio_str, "%u", &inst_ratio) != 1 || !inst_ratio ||
        inst_ratio > 100)
      FATAL("Bad value of AFL_INST_RATIO (must be between 1 and 100)");

  }

  /* Get globals for the SHM region and the previous location. Note that
     __afl_prev_loc is thread-local. */

  GlobalVariable *AFLMapPtr =
      new GlobalVariable(/*Module=*/M, 
                         /*Type=*/PointerType::get(Int8Ty, 0), 
                         /*isConstant=*/false,
                         /*Linkage=*/GlobalValue::ExternalLinkage, 
                         /*Initializer=*/0,  //has Initializer, specified below
                         /*Name=*/"__afl_area_ptr"); 

  GlobalVariable *AFLMemWritePtr = 
      new GlobalVariable(M, PointerType::get(Int32Ty, 0), false,
                        GlobalValue::ExternalLinkage, 0, "__afl_memwrite_ptr");

  GlobalVariable *AFLMemReadPtr = 
      new GlobalVariable(M, PointerType::get(Int32Ty, 0), false,
                        GlobalValue::ExternalLinkage, 0, "__afl_memread_ptr");
  
  GlobalVariable *AFLPrevLoc = new GlobalVariable(
      M, Int32Ty, false, GlobalValue::ExternalLinkage, 0, "__afl_prev_loc",
      0, GlobalVariable::GeneralDynamicTLSModel, 0, false);

  /* Instrument all the things! */

  int inst_blocks = 0;
  for (auto &F : M){
    for (auto &BB : F) {
      int mem_read_cnt = 0;
      int mem_write_cnt= 0;

      BasicBlock::iterator IP = BB.getFirstInsertionPt(); 
      //返回这个基本块中适合插入non-PHI指令的第一条指令(跳过所有PHI)【PHI用来选择操作哪一个版本的变量】
      IRBuilder<> IRB(&(*IP));

      if (AFL_R(100) >= inst_ratio) continue;

      for (auto Inst = BB.begin(); Inst != BB.end(); Inst++) { //基本块的迭代器指向每条指令
        Instruction &inst = *Inst;

        if(inst.mayReadFromMemory()){
          mem_read_cnt++;
          // outs() << "read mem inst:" << inst << "\n";
        }

        if(inst.mayWriteToMemory()){
          mem_write_cnt++;
          // outs() << "write mem inst:" << inst << "\n";
        }
      }

      /* Make up cur_loc */

      unsigned int cur_loc = AFL_R(MAP_SIZE);

      ConstantInt *CurLoc = ConstantInt::get(Int32Ty, cur_loc); //初始化一个指针指向这个int

      /* Load prev_loc */

      LoadInst *PrevLoc = IRB.CreateLoad(AFLPrevLoc); //从 AFLPrevLoc 取值
      PrevLoc->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None)); 
      //第一个参数是元数据的类型，第二个参数是要添加元数据的目标节点
      // C 是这个 module 的 context，get 返回 static MDTuple*
      
      
      Value *PrevLocCasted = IRB.CreateZExt(PrevLoc, IRB.getInt32Ty()); // 转换 PrevLoc 的类型

      /* Load SHM pointer */

      LoadInst *MapPtr = IRB.CreateLoad(AFLMapPtr);
      MapPtr->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      Value *MapPtrIdx =
          IRB.CreateGEP(MapPtr, IRB.CreateXor(PrevLocCasted, CurLoc)); //相当于数组取值，MapPtr[PrevLoc^Curloc]
      //并通过CreateGEP函数来获取共享内存里指定index的地址
      //这个index通过cur_loc和prev_loc取xor计算得到。

      /* Update bitmap */

      LoadInst *Counter = IRB.CreateLoad(MapPtrIdx); //取出 MapPtrIdx 这个共享内存地址的值
      Counter->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      Value *Incr = IRB.CreateAdd(Counter, ConstantInt::get(Int8Ty, 1)); // 加 1
      IRB.CreateStore(Incr, MapPtrIdx)
          ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));  // 写回

      //Load and update mem read/write map
      if(mem_read_cnt > 0){
        LoadInst *MemReadPtr = IRB.CreateLoad(AFLMemReadPtr);
        MemReadPtr->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
        //破案了，是这条边的内存读计数，因为下标也用的是 prevLoc^curLoc
        Value *MemReadPtrIdx = IRB.CreateGEP(MemReadPtr, IRB.CreateXor(PrevLocCasted, CurLoc)); 
        LoadInst *MemReadCount = IRB.CreateLoad(MemReadPtrIdx);
        MemReadCount->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
        Value *MemReadIncr = IRB.CreateAdd(MemReadCount, ConstantInt::get(Int32Ty, mem_read_cnt));
        IRB.CreateStore(MemReadIncr, MemReadPtrIdx)
            ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      }
      if(mem_write_cnt > 0){
        LoadInst *MemWritePtr = IRB.CreateLoad(AFLMemWritePtr);
        MemWritePtr->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
        //同样地，内存写计数
        Value *MemWritePtrIdx = IRB.CreateGEP(MemWritePtr, IRB.CreateXor(PrevLocCasted, CurLoc));
      
        LoadInst *MemWriteCount = IRB.CreateLoad(MemWritePtrIdx);
        MemWriteCount->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
        Value *MemWriteIncr = IRB.CreateAdd(MemWriteCount, ConstantInt::get(Int32Ty, mem_write_cnt));
        IRB.CreateStore(MemWriteIncr, MemWritePtrIdx)
            ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      }

      /* Set prev_loc to cur_loc >> 1 */

      StoreInst *Store =
          IRB.CreateStore(ConstantInt::get(Int32Ty, cur_loc >> 1), AFLPrevLoc);
      Store->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

      inst_blocks++;

    }
  }

  /* Say something nice. */

  if (!be_quiet) {

    if (!inst_blocks) WARNF("No instrumentation targets found.");
    else OKF("Instrumented %u locations (%s mode, ratio %u%%).",
             inst_blocks, getenv("AFL_HARDEN") ? "hardened" :
             ((getenv("AFL_USE_ASAN") || getenv("AFL_USE_MSAN")) ?
              "ASAN/MSAN" : "non-hardened"), inst_ratio);

  }

  return true;

}

//注册自定义类 registerAFLPass，
static void registerAFLPass(const PassManagerBuilder &,
                            legacy::PassManagerBase &PM) {

  PM.add(new AFLCoverage());

}


static RegisterStandardPasses RegisterAFLPass(
    PassManagerBuilder::EP_OptimizerLast, registerAFLPass);

static RegisterStandardPasses RegisterAFLPass0(
    PassManagerBuilder::EP_EnabledOnOptLevel0, registerAFLPass);
