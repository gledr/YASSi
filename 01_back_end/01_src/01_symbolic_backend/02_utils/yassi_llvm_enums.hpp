#ifndef YASSI_LLVM_ENUMS_HPP
#define YASSI_LLVM_ENUMS_HPP

enum LLVMIntPredicate{
  LLVMIntEQ = 32, /**< equal */
  LLVMIntNE,      /**< not equal */
  LLVMIntUGT,     /**< unsigned greater than */
  LLVMIntUGE,     /**< unsigned greater or equal */
  LLVMIntULT,     /**< unsigned less than */
  LLVMIntULE,     /**< unsigned less or equal */
  LLVMIntSGT,     /**< signed greater than */
  LLVMIntSGE,     /**< signed greater or equal */
  LLVMIntSLT,     /**< signed less than */
  LLVMIntSLE      /**< signed less or equal */
};

enum LLVMRealPredicate{
  LLVMRealPredicateFalse, /**< Always false (always folded) */
  LLVMRealOEQ,            /**< True if ordered and equal */
  LLVMRealOGT,            /**< True if ordered and greater than */
  LLVMRealOGE,            /**< True if ordered and greater than or equal */
  LLVMRealOLT,            /**< True if ordered and less than */
  LLVMRealOLE,            /**< True if ordered and less than or equal */
  LLVMRealONE,            /**< True if ordered and operands are unequal */
  LLVMRealORD,            /**< True if ordered (no nans) */
  LLVMRealUNO,            /**< True if unordered: isnan(X) | isnan(Y) */
  LLVMRealUEQ,            /**< True if unordered or equal */
  LLVMRealUGT,            /**< True if unordered or greater than */
  LLVMRealUGE,            /**< True if unordered, greater than, or equal */
  LLVMRealULT,            /**< True if unordered or less than */
  LLVMRealULE,            /**< True if unordered, less than, or equal */
  LLVMRealUNE,            /**< True if unordered or not equal */
  LLVMRealPredicateTrue   /**< Always true (always folded) */
} ;

enum LLVMOpcode {
  /* Terminator Instructions */
  LLVMRet            = 1,
  LLVMBr             = 2,
  LLVMSwitch         = 3,
  LLVMIndirectBr     = 4,
  LLVMInvoke         = 5,
  /* removed 6 due to API changes */
  LLVMUnreachable    = 7,

  /* Standard Binary Operators */
  LLVMAdd            = 11,
  LLVMFAdd           = 12,
  LLVMSub            = 13,
  LLVMFSub           = 14,
  LLVMMul            = 15,
  LLVMFMul           = 16,
  LLVMUDiv           = 17,
  LLVMSDiv           = 18,
  LLVMFDiv           = 19,
  LLVMURem           = 20,
  LLVMSRem           = 21,
  LLVMFRem           = 22,

  /* Logical Operators */
  LLVMShl            = 23,
  LLVMLShr           = 24,
  LLVMAShr           = 25,
  LLVMAnd            = 26,
  LLVMOr             = 27,
  LLVMXor            = 28,

  /* Memory Operators */
  LLVMAlloca         = 29,
  LLVMLoad           = 30,
  LLVMStore          = 31,
  LLVMGetElementPtr  = 32,

  /* Cast Operators */
  LLVMTrunc          = 33,
  LLVMZExt           = 34,
  LLVMSExt           = 35,
  LLVMFPToUI         = 36,
  LLVMFPToSI         = 37,
  LLVMUIToFP         = 38,
  LLVMSIToFP         = 39,
  LLVMFPTrunc        = 40,
  LLVMFPExt          = 41,
  LLVMPtrToInt       = 42,
  LLVMIntToPtr       = 43,
  LLVMBitCast        = 44,
  LLVMAddrSpaceCast  = 45,

  /* Other Operators */
  LLVMICmp           = 46,
  LLVMFCmp           = 47,
  LLVMPHI            = 48,
  LLVMCall           = 49,
  LLVMSelect         = 50,
  LLVMUserOp1        = 51,
  LLVMUserOp2        = 52,
  LLVMVAArg          = 53,
  LLVMExtractElement = 54,
  LLVMInsertElement  = 55,
  LLVMShuffleVector  = 56,
  LLVMExtractValue   = 57,
  LLVMInsertValue    = 58,

  /* Atomic operators */
  LLVMFence          = 59,
  LLVMAtomicCmpXchg  = 60,
  LLVMAtomicRMW      = 61,

  /* Exception Handling Operators */
  LLVMResume         = 62,
  LLVMLandingPad     = 63,
  LLVMCleanupRet     = 64,
  LLVMCatchRet       = 65,
  LLVMCatchPad       = 66,
  LLVMCleanupPad     = 67,
  LLVMCatchSwitch    = 68
};



#endif /* YASSI_LLVM_ENUMS_HPP */
