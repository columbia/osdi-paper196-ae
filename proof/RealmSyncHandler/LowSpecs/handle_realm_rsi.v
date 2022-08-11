Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import PSCIHandler.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition handle_realm_rsi_spec0 (rec: Pointer) (adt: RData) : option (RData * Z) :=
	  when' function_id == get_rec_regs_spec rec 0 adt;
	  when' arg1 == get_rec_regs_spec rec 1 adt;
	  when' arg2 == get_rec_regs_spec rec 2 adt;
	  when' arg3 == get_rec_regs_spec rec 3 adt;
    rely is_int64 function_id; rely is_int64 arg1; rely is_int64 arg2; rely is_int64 arg3;
    if function_id =? SMC_RSI_ABI_VERSION then
		  when adt == set_rec_regs_spec rec 1 (VZ64 RSI_ABI_VERSION) adt;
		  when adt == set_rec_regs_spec rec 0 (VZ64 STATUS_SUCCESS) adt;
      Some (adt, 1)
    else
      if ((function_id >=? SMC32_PSCI_BASE) && (function_id <=? SMC32_PSCI_MAX)) ||
         ((function_id >=? SMC64_PSCI_BASE) && (function_id <=? SMC64_PSCI_MAX))
      then
		    when adt == psci_rsi_spec rec function_id (VZ64 arg1) (VZ64 arg2) (VZ64 arg3) adt;
        when' x0 == get_psci_result_x0_spec adt;
        rely is_int64 x0;
		    when adt == set_rec_regs_spec rec 0 (VZ64 x0) adt;
        when' x1 == get_psci_result_x1_spec adt;
        rely is_int64 x1;
		    when adt == set_rec_regs_spec rec 1 (VZ64 x1) adt;
        when' x2 == get_psci_result_x2_spec adt;
        rely is_int64 x2;
		    when adt == set_rec_regs_spec rec 2 (VZ64 x2) adt;
        when' x3 == get_psci_result_x3_spec adt;
        rely is_int64 x3;
		    when adt == set_rec_regs_spec rec 3 (VZ64 x3) adt;
        when forward == get_psci_result_forward_psci_call_spec adt;
        rely is_int forward;
        if forward =? 1 then
			    when adt == set_rec_run_exit_reason_spec (VZ64 EXIT_REASON_PSCI) adt;
			    when adt == set_rec_run_gprs_spec 0 (VZ64 function_id) adt;
          when' x1 == get_psci_result_forward_x1_spec adt;
          rely is_int64 x1;
          when adt == set_rec_run_gprs_spec 1 (VZ64 x1) adt;
          when' x2 == get_psci_result_forward_x2_spec adt;
          rely is_int64 x2;
          when adt == set_rec_run_gprs_spec 2 (VZ64 x2) adt;
          when' x3 == get_psci_result_forward_x3_spec adt;
          rely is_int64 x3;
          when adt == set_rec_run_gprs_spec 3 (VZ64 x3) adt;
          when adt == set_rec_run_gprs_spec 4 (VZ64 0) adt;
          when adt == set_rec_run_gprs_spec 5 (VZ64 0) adt;
          when adt == set_rec_run_gprs_spec 6 (VZ64 0) adt;
          Some (adt, 0)
        else
          Some (adt, 1)
		  else
		    when adt == set_rec_regs_spec rec 0 (VZ64 SMC_RETURN_UNKNOWN_FUNCTION) adt;
        Some (adt, 1).

End SpecLow.
