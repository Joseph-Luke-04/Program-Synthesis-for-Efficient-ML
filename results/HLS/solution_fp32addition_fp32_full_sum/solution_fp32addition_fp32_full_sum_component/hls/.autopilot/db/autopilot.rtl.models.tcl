set SynModuleInfo {
  {SRCNAME fp32_normaliser MODELNAME fp32_normaliser RTLNAME fp32_sum_fp32_normaliser}
  {SRCNAME fp32_sum MODELNAME fp32_sum RTLNAME fp32_sum IS_TOP 1
    SUBMODULES {
      {MODELNAME fp32_sum_sparsemux_7_2_25_1_1 RTLNAME fp32_sum_sparsemux_7_2_25_1_1 BINDTYPE op TYPE sparsemux IMPL onehotencoding_realdef}
    }
  }
}
