Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import PendingCheck.Layer.
Require Import CtxtSwitchAux.Code.restore_ns_state_sysreg_state.

Require Import CtxtSwitchAux.LowSpecs.restore_ns_state_sysreg_state.

Local Open Scope Z_scope.

Section CodeProof.

  Context `{real_params: RealParams}.
  Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
  Context `{Hmwd: UseMemWithData memb}.

  Let mem := mwd (cdata RData).

  Context `{Hstencil: Stencil}.
  Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
  Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.

  Let L : compatlayer (cdata RData) :=
    _get_ns_state ↦ gensem get_ns_state_spec
      ⊕ _sysreg_write ↦ gensem sysreg_write_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_get_ns_state: block.
    Hypothesis h_get_ns_state_s : Genv.find_symbol ge _get_ns_state = Some b_get_ns_state.
    Hypothesis h_get_ns_state_p : Genv.find_funct_ptr ge b_get_ns_state
                                  = Some (External (EF_external _get_ns_state
                                                   (signature_of_type (Tcons tuint Tnil) tulong cc_default))
                                         (Tcons tuint Tnil) tulong cc_default).
    Local Opaque get_ns_state_spec.

    Variable b_sysreg_write: block.
    Hypothesis h_sysreg_write_s : Genv.find_symbol ge _sysreg_write = Some b_sysreg_write.
    Hypothesis h_sysreg_write_p : Genv.find_funct_ptr ge b_sysreg_write
                                  = Some (External (EF_external _sysreg_write
                                                   (signature_of_type (Tcons tuint (Tcons tulong Tnil)) tvoid cc_default))
                                         (Tcons tuint (Tcons tulong Tnil)) tvoid cc_default).
    Local Opaque sysreg_write_spec.

    Lemma restore_ns_state_sysreg_state_body_correct:
      forall m d d' env le
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (Hspec: restore_ns_state_sysreg_state_spec0  d = Some d'),
           exists le', (exec_stmt ge env le ((m, d): mem) restore_ns_state_sysreg_state_body E0 le' (m, d') Out_normal).
    Proof.
      solve_code_proof Hspec restore_ns_state_sysreg_state_body.
      eexists.

      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. big_vcgen.
      solve_func64 z0. reflexivity.
      symmetry. sstep. assumption. somega.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. solve_proof_low.

      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. big_vcgen.
      solve_func64 z2. reflexivity.
      symmetry. sstep. assumption. somega.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. solve_proof_low.

      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. big_vcgen.
      solve_func64 z4. reflexivity.
      symmetry. sstep. assumption. somega.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. solve_proof_low.

      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. big_vcgen.
      solve_func64 z6. reflexivity.
      symmetry. sstep. assumption. somega.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. solve_proof_low.

      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. big_vcgen.
      solve_func64 z8. reflexivity.
      symmetry. sstep. assumption. somega.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. solve_proof_low.

      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. big_vcgen.
      solve_func64 z10. reflexivity.
      symmetry. sstep. assumption. somega.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. solve_proof_low.

      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. big_vcgen.
      solve_func64 z12. reflexivity.
      symmetry. sstep. assumption. somega.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. solve_proof_low.

      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. big_vcgen.
      solve_func64 z14. reflexivity.
      symmetry. sstep. assumption. somega.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. solve_proof_low.

      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. big_vcgen.
      solve_func64 z16. reflexivity.
      symmetry. sstep. assumption. somega.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. solve_proof_low.

      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. big_vcgen.
      solve_func64 z18. reflexivity.
      symmetry. sstep. assumption. somega.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. solve_proof_low.

      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. big_vcgen.
      solve_func64 z20. reflexivity.
      symmetry. sstep. assumption. somega.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. solve_proof_low.

      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. big_vcgen.
      solve_func64 z22. reflexivity.
      symmetry. sstep. assumption. somega.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. solve_proof_low.

      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. big_vcgen.
      solve_func64 z24. reflexivity.
      symmetry. sstep. assumption. somega.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. solve_proof_low.

      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. big_vcgen.
      solve_func64 z26. reflexivity.
      symmetry. sstep. assumption. somega.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. solve_proof_low.

      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. big_vcgen.
      solve_func64 z28. reflexivity.
      symmetry. sstep. assumption. somega.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. solve_proof_low.

      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. big_vcgen.
      solve_func64 z30. reflexivity.
      symmetry. sstep. assumption. somega.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. solve_proof_low.

      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. big_vcgen.
      solve_func64 z32. reflexivity.
      symmetry. sstep. assumption. somega.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. solve_proof_low.

      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. big_vcgen.
      solve_func64 z34. reflexivity.
      symmetry. sstep. assumption. somega.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. solve_proof_low.

      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. big_vcgen.
      solve_func64 z36. reflexivity.
      symmetry. sstep. assumption. somega.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. solve_proof_low.

      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. big_vcgen.
      solve_func64 z38. reflexivity.
      symmetry. sstep. assumption. somega.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. solve_proof_low.

      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. big_vcgen.
      solve_func64 z40. reflexivity.
      symmetry. sstep. assumption. somega.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. solve_proof_low.

      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. big_vcgen.
      solve_func64 z42. reflexivity.
      symmetry. sstep. assumption. somega.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. solve_proof_low.

      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. big_vcgen.
      solve_func64 z44. reflexivity.
      symmetry. sstep. assumption. somega.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. solve_proof_low.

      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. big_vcgen.
      solve_func64 z46. reflexivity.
      symmetry. sstep. assumption. somega.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. solve_proof_low.

      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. big_vcgen.
      solve_func64 z48. reflexivity.
      symmetry. sstep. assumption. somega.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. solve_proof_low.

      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. big_vcgen.
      solve_func64 z50. reflexivity.
      symmetry. sstep. assumption. somega.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. solve_proof_low.

      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. big_vcgen.
      solve_func64 z52. reflexivity.
      symmetry. sstep. assumption. somega.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. solve_proof_low.

      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. big_vcgen.
      solve_func64 z54. reflexivity.
      symmetry. sstep. assumption. somega.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. solve_proof_low.

      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. big_vcgen.
      solve_func64 z56. reflexivity.
      symmetry. sstep. assumption. somega.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. solve_proof_low.

      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. big_vcgen.
      solve_func64 z58. reflexivity.
      symmetry. sstep. assumption. somega.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. solve_proof_low.

      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. big_vcgen.
      solve_func64 z60. reflexivity.
      symmetry. sstep. assumption. somega.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. solve_proof_low.

      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. big_vcgen.
      solve_func64 z62. reflexivity.
      symmetry. sstep. assumption. somega.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. solve_proof_low.

      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. big_vcgen.
      solve_func64 z64. reflexivity.
      symmetry. sstep. assumption. somega.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. solve_proof_low.

      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. big_vcgen.
      solve_func64 z66. reflexivity.
      symmetry. sstep. assumption. somega.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. solve_proof_low.

      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. big_vcgen.
      solve_func64 z68. reflexivity.
      symmetry. sstep. assumption. somega.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. solve_proof_low.

      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. big_vcgen.
      solve_func64 z70. reflexivity.
      symmetry. sstep. assumption. somega.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. solve_proof_low.

      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. big_vcgen.
      solve_func64 z72. reflexivity.
      symmetry. sstep. assumption. somega.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. solve_proof_low.

      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. big_vcgen.
      solve_func64 z74. reflexivity.
      symmetry. sstep. assumption. somega.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen. vcgen.
      vcgen. vcgen. vcgen. vcgen. vcgen. solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
