Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RealmSyncHandler.Spec.
Require Import RealmSyncHandler.Layer.
Require Import RealmExitHandlerAux.Code.handle_exception_sync.

Require Import RealmExitHandlerAux.LowSpecs.handle_exception_sync.

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
    _sysreg_read ↦ gensem sysreg_read_spec
      ⊕ _set_rec_run_esr ↦ gensem set_rec_run_esr_spec
      ⊕ _set_rec_last_run_info_esr ↦ gensem set_rec_last_run_info_esr_spec
      ⊕ _set_rec_run_gprs ↦ gensem set_rec_run_gprs_spec
      ⊕ _get_rec_regs ↦ gensem get_rec_regs_spec
      ⊕ _sysreg_write ↦ gensem sysreg_write_spec
      ⊕ _handle_realm_rsi ↦ gensem handle_realm_rsi_spec
      ⊕ _handle_sysreg_access_trap ↦ gensem handle_sysreg_access_trap_spec
      ⊕ _handle_instruction_abort ↦ gensem handle_instruction_abort_spec
      ⊕ _set_rec_run_far ↦ gensem set_rec_run_far_spec
      ⊕ _set_rec_run_hpfar ↦ gensem set_rec_run_hpfar_spec
      ⊕ _handle_data_abort ↦ gensem handle_data_abort_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_sysreg_read: block.
    Hypothesis h_sysreg_read_s : Genv.find_symbol ge _sysreg_read = Some b_sysreg_read.
    Hypothesis h_sysreg_read_p : Genv.find_funct_ptr ge b_sysreg_read
                                 = Some (External (EF_external _sysreg_read
                                                  (signature_of_type (Tcons tuint Tnil) tulong cc_default))
                                        (Tcons tuint Tnil) tulong cc_default).
    Local Opaque sysreg_read_spec.

    Variable b_set_rec_run_esr: block.
    Hypothesis h_set_rec_run_esr_s : Genv.find_symbol ge _set_rec_run_esr = Some b_set_rec_run_esr.
    Hypothesis h_set_rec_run_esr_p : Genv.find_funct_ptr ge b_set_rec_run_esr
                                     = Some (External (EF_external _set_rec_run_esr
                                                      (signature_of_type (Tcons tulong Tnil) tvoid cc_default))
                                            (Tcons tulong Tnil) tvoid cc_default).
    Local Opaque set_rec_run_esr_spec.

    Variable b_set_rec_last_run_info_esr: block.
    Hypothesis h_set_rec_last_run_info_esr_s : Genv.find_symbol ge _set_rec_last_run_info_esr = Some b_set_rec_last_run_info_esr.
    Hypothesis h_set_rec_last_run_info_esr_p : Genv.find_funct_ptr ge b_set_rec_last_run_info_esr
                                               = Some (External (EF_external _set_rec_last_run_info_esr
                                                                (signature_of_type (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default))
                                                      (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default).
    Local Opaque set_rec_last_run_info_esr_spec.

    Variable b_set_rec_run_gprs: block.
    Hypothesis h_set_rec_run_gprs_s : Genv.find_symbol ge _set_rec_run_gprs = Some b_set_rec_run_gprs.
    Hypothesis h_set_rec_run_gprs_p : Genv.find_funct_ptr ge b_set_rec_run_gprs
                                      = Some (External (EF_external _set_rec_run_gprs
                                                       (signature_of_type (Tcons tuint (Tcons tulong Tnil)) tvoid cc_default))
                                             (Tcons tuint (Tcons tulong Tnil)) tvoid cc_default).
    Local Opaque set_rec_run_gprs_spec.

    Variable b_get_rec_regs: block.
    Hypothesis h_get_rec_regs_s : Genv.find_symbol ge _get_rec_regs = Some b_get_rec_regs.
    Hypothesis h_get_rec_regs_p : Genv.find_funct_ptr ge b_get_rec_regs
                                  = Some (External (EF_external _get_rec_regs
                                                   (signature_of_type (Tcons Tptr (Tcons tuint Tnil)) tulong cc_default))
                                         (Tcons Tptr (Tcons tuint Tnil)) tulong cc_default).
    Local Opaque get_rec_regs_spec.

    Variable b_sysreg_write: block.
    Hypothesis h_sysreg_write_s : Genv.find_symbol ge _sysreg_write = Some b_sysreg_write.
    Hypothesis h_sysreg_write_p : Genv.find_funct_ptr ge b_sysreg_write
                                  = Some (External (EF_external _sysreg_write
                                                   (signature_of_type (Tcons tuint (Tcons tulong Tnil)) tvoid cc_default))
                                         (Tcons tuint (Tcons tulong Tnil)) tvoid cc_default).
    Local Opaque sysreg_write_spec.

    Variable b_handle_realm_rsi: block.
    Hypothesis h_handle_realm_rsi_s : Genv.find_symbol ge _handle_realm_rsi = Some b_handle_realm_rsi.
    Hypothesis h_handle_realm_rsi_p : Genv.find_funct_ptr ge b_handle_realm_rsi
                                      = Some (External (EF_external _handle_realm_rsi
                                                       (signature_of_type (Tcons Tptr Tnil) tuint cc_default))
                                             (Tcons Tptr Tnil) tuint cc_default).
    Local Opaque handle_realm_rsi_spec.

    Variable b_handle_sysreg_access_trap: block.
    Hypothesis h_handle_sysreg_access_trap_s : Genv.find_symbol ge _handle_sysreg_access_trap = Some b_handle_sysreg_access_trap.
    Hypothesis h_handle_sysreg_access_trap_p : Genv.find_funct_ptr ge b_handle_sysreg_access_trap
                                               = Some (External (EF_external _handle_sysreg_access_trap
                                                                (signature_of_type (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default))
                                                      (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default).
    Local Opaque handle_sysreg_access_trap_spec.

    Variable b_handle_instruction_abort: block.
    Hypothesis h_handle_instruction_abort_s : Genv.find_symbol ge _handle_instruction_abort = Some b_handle_instruction_abort.
    Hypothesis h_handle_instruction_abort_p : Genv.find_funct_ptr ge b_handle_instruction_abort
                                              = Some (External (EF_external _handle_instruction_abort
                                                               (signature_of_type (Tcons Tptr (Tcons tulong Tnil)) tuint cc_default))
                                                     (Tcons Tptr (Tcons tulong Tnil)) tuint cc_default).
    Local Opaque handle_instruction_abort_spec.

    Variable b_set_rec_run_far: block.
    Hypothesis h_set_rec_run_far_s : Genv.find_symbol ge _set_rec_run_far = Some b_set_rec_run_far.
    Hypothesis h_set_rec_run_far_p : Genv.find_funct_ptr ge b_set_rec_run_far
                                     = Some (External (EF_external _set_rec_run_far
                                                      (signature_of_type (Tcons tulong Tnil) tvoid cc_default))
                                            (Tcons tulong Tnil) tvoid cc_default).
    Local Opaque set_rec_run_far_spec.

    Variable b_set_rec_run_hpfar: block.
    Hypothesis h_set_rec_run_hpfar_s : Genv.find_symbol ge _set_rec_run_hpfar = Some b_set_rec_run_hpfar.
    Hypothesis h_set_rec_run_hpfar_p : Genv.find_funct_ptr ge b_set_rec_run_hpfar
                                       = Some (External (EF_external _set_rec_run_hpfar
                                                        (signature_of_type (Tcons tulong Tnil) tvoid cc_default))
                                              (Tcons tulong Tnil) tvoid cc_default).
    Local Opaque set_rec_run_hpfar_spec.

    Variable b_handle_data_abort: block.
    Hypothesis h_handle_data_abort_s : Genv.find_symbol ge _handle_data_abort = Some b_handle_data_abort.
    Hypothesis h_handle_data_abort_p : Genv.find_funct_ptr ge b_handle_data_abort
                                       = Some (External (EF_external _handle_data_abort
                                                        (signature_of_type (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default))
                                              (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default).
    Local Opaque handle_data_abort_spec.


    Lemma handle_exception_sync_body_correct:
      forall m d d' env le rec_base rec_offset res
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTrec: PTree.get _rec le = Some (Vptr rec_base (Int.repr rec_offset)))
             (Hspec: handle_exception_sync_spec0 (rec_base, rec_offset) d = Some (d',Int.unsigned res)),
      exists le', (exec_stmt ge env le ((m, d): mem) handle_exception_sync_body E0 le' (m, d') (Out_return (Some (Vint res, tuint)))).
    Proof.
      solve_code_proof Hspec handle_exception_sync_body.
      - eexists; solve_proof_low.
      - get_loop_body. clear_hyp.
        set (Hloop := C9). simpl. solve_proof_low.
        remember
          (PTree.set _info (Vlong (Int64.repr (Z.land z0 (Z.lor 4227858432 65535))))
              (PTree.set _i (Vint res)
                (PTree.set _ec (Vlong (Int64.repr (Z.land z0 4227858432)))
                    (PTree.set _esr (Vlong (Int64.repr z0)) (PTree.set _t'1 (Vlong (Int64.repr z0)) le)))))
          as le_loop.
        remember 7 as num.
        set (P := fun le0 m0 => m0 = (m, r0) /\ le0 = le_loop).
        set (Q := fun (le0: temp_env) m0 => m0 = (m, d')).
        set (Inv := fun le0 m0 n => exists i' adt',
                        handle_exception_sync_loop0 (Z.to_nat (num - n))
                                                    (Int.unsigned res) rec_base rec_offset r0 =
                          Some (Int.unsigned i', adt') /\ Int.unsigned i' = num - n /\
                          m0 = (m, adt') /\ 0 <= n /\ n <= num /\ le0 ! _i = Some (Vint i') /\
                          le0 ! _rec = Some (Vptr rec_base (Int.repr rec_offset))).
        assert(loop_succ: forall N, Z.of_nat N <= num -> exists i' adt',
                    handle_exception_sync_loop0 (Z.to_nat (num - Z.of_nat N)) (Int.unsigned res) rec_base rec_offset r0
                    = Some (Int.unsigned i', adt')).
        { add_int Hloop z1; try somega.
          induction N. rewrite Z.sub_0_r. rewrite Hloop. intros. repeat eexists; reflexivity.
          intros. erewrite loop_ind_sub1 in IHN; try omega.
          rewrite Nat2Z.inj_succ, succ_plus_1 in H.
          assert(Hcc: Z.of_nat N <= num) by omega.
          apply IHN in Hcc. destruct Hcc as (? & ? & Hnext).
          Local Opaque Z.of_nat. simpl in Hnext. clear Heqle_loop.
          simpl_func Hnext; try add_int' z; repeat eexists; try somega. }
        assert (T: LoopProofSimpleWhile.t (external_calls_ops := CompatExternalCalls.compatlayer_extcall_ops L) cond body ge (PTree.empty _) P Q).
        { apply LoopProofSimpleWhile.make with (W:=Z) (lt:=fun z1 z2 => (0 <= z2 /\ z1 < z2)) (I:=Inv).
          - apply Zwf_well_founded.
          - unfold P, Inv. intros ? ? CC. destruct CC as [CC1 CC2].
            rewrite CC2 in *. exists num.
            replace (num - num) with 0 by omega. simpl. add_int' 0; try somega.
            rewrite Heqnum. rewrite Heqle_loop.
            repeat eexists; first [reflexivity|assumption|solve_proof_low].
          - intros ? ? ? I. unfold Inv in I. destruct I as (? & ? & ? & ? & ? & ? & ? & ? & ?).
            set (Hnow := H).
            rewrite Heqbody, Heqcond in *.
            destruct (n >? 0) eqn:Hn; bool_rel.
            + eexists. eexists. split_and.
              * solve_proof_low.
              * solve_proof_low.
              * intro CC. inversion CC.
              * assert(Hlx: Z.of_nat (Z.to_nat (n-1)) <= num) by (rewrite Z2Nat.id; omega).
                apply loop_succ in Hlx. rewrite Z2Nat.id in Hlx; try omega.
                intro. destruct Hlx as (? & ? & Hnext). duplicate Hnext.
                rewrite loop_nat_sub1 in Hnext; try somega.
                simpl in Hnext. rewrite Hnow in Hnext.
                autounfold in Hnext; repeat simpl_hyp Hnext;
                  repeat destruct_con; bool_rel; contra; inversion Hnext.
                rewrite H9, H10 in *; eexists; eexists; split. solve_proof_low.
                exists (n-1); split. split; solve_proof_low.
                solve_proof_low; unfold Inv; repeat eexists; first[eassumption|solve_proof_low].
            + eexists. eexists. split_and.
              * solve_proof_low.
              * solve_proof_low.
              * intro. unfold Q.
                assert (n=0) by omega. clear Heqle_loop. subst.
                sstep. rewrite Hloop in Hnow. inv Hnow.
                split_and; first[reflexivity|solve_proof_low].
              * intro CC. inversion CC. }
          assert (Pre: P le_loop (m, r0)) by (split; reflexivity).
          pose proof (LoopProofSimpleWhile.termination _ _ _ _ _ _ T _ (m, r0) Pre) as LoopProof.
          destruct LoopProof as (le' & m' & (exec & Post)).
          unfold exec_stmt in exec. rewrite Heqle_loop in exec.
          unfold Q in Post. rewrite Post in exec.
        eexists; solve_proof_low.
      - eexists; solve_proof_low.
      - eexists; solve_proof_low.
      - eexists; solve_proof_low.
      - eexists; solve_proof_low.
      - eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
