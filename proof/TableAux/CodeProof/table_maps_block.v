Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RunSMC.Layer.
Require Import TableAux.Code.table_maps_block.

Require Import TableAux.LowSpecs.table_maps_block.

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
    _pgte_read ↦ gensem pgte_read_spec
      ⊕ _entry_to_phys ↦ gensem entry_to_phys_spec
      ⊕ _addr_is_level_aligned ↦ gensem addr_is_level_aligned_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_pgte_read: block.
    Hypothesis h_pgte_read_s : Genv.find_symbol ge _pgte_read = Some b_pgte_read.
    Hypothesis h_pgte_read_p : Genv.find_funct_ptr ge b_pgte_read
                               = Some (External (EF_external _pgte_read
                                                (signature_of_type (Tcons Tptr (Tcons tulong Tnil)) tulong cc_default))
                                      (Tcons Tptr (Tcons tulong Tnil)) tulong cc_default).
    Local Opaque pgte_read_spec.

    Variable b_entry_to_phys: block.
    Hypothesis h_entry_to_phys_s : Genv.find_symbol ge _entry_to_phys = Some b_entry_to_phys.
    Hypothesis h_entry_to_phys_p : Genv.find_funct_ptr ge b_entry_to_phys
                                   = Some (External (EF_external _entry_to_phys
                                                    (signature_of_type (Tcons tulong (Tcons tulong Tnil)) tulong cc_default))
                                          (Tcons tulong (Tcons tulong Tnil)) tulong cc_default).
    Local Opaque entry_to_phys_spec.

    Variable b_addr_is_level_aligned: block.
    Hypothesis h_addr_is_level_aligned_s : Genv.find_symbol ge _addr_is_level_aligned = Some b_addr_is_level_aligned.
    Hypothesis h_addr_is_level_aligned_p : Genv.find_funct_ptr ge b_addr_is_level_aligned
                                           = Some (External (EF_external _addr_is_level_aligned
                                                            (signature_of_type (Tcons tulong (Tcons tulong Tnil)) tuint cc_default))
                                                  (Tcons tulong (Tcons tulong Tnil)) tuint cc_default).
    Local Opaque addr_is_level_aligned_spec.


    Ltac solve_func64 val :=
      try unfold Monad.bind; try unfold ret; simpl;
      match goal with
      | [|- match ?v with | Some _ => _ | None => None end = _] =>
          replace v with (Some (VZ64 (Int64.unsigned (Int64.repr val))))
      end.

    Ltac solve_func val :=
      try unfold Monad.bind; try unfold ret; simpl;
      match goal with
      | [|- match ?v with | Some _ => _ | None => None end = _] =>
          replace v with (Some (Int.unsigned (Int.repr val)))
      end.

    Lemma table_maps_block_body_correct:
      forall m d env le table_base table_offset level ipa_state res
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTtable: PTree.get _table le = Some (Vptr table_base (Int.repr table_offset)))
             (HPTlevel: PTree.get _level le = Some (Vlong level))
             (HPTipa_state: PTree.get _ipa_state le = Some (Vlong ipa_state))
             (Hspec: table_maps_block_spec0 (table_base, table_offset) (VZ64 (Int64.unsigned level)) (VZ64 (Int64.unsigned ipa_state)) d = Some (Int.unsigned res)),
           exists le', (exec_stmt ge env le ((m, d): mem) table_maps_block_body E0 le' (m, d) (Out_return (Some (Vint res, tuint)))).
    Proof.
      solve_code_proof Hspec table_maps_block_body.
      - eexists. repeat big_vcgen.
        solve_func64 z0. reflexivity.
        symmetry. repeat sstep. assumption. somega.
        solve_func64 z2. reflexivity.
        symmetry. repeat sstep.
        rewrite C8. reflexivity.
        somega. somega. somega. somega.
        solve_proof_low.
        simpl. solve_proof_low.
      - get_loop_body. clear_hyp.
        set (Hloop := C11). simpl; solve_proof_low.
        remember
            (PTree.set _i (Vint (Int.repr 0))
                (PTree.set _ret (Vint (Int.repr 1))
                  (PTree.set _t'5 (Vint (Int.repr z3))
                      (PTree.set _base_pa (Vlong (Int64.repr z2))
                        (PTree.set _t'2 (Vlong (Int64.repr z2))
                            (PTree.set _pgte (Vlong (Int64.repr z0))
                              (PTree.set _t'1 (Vlong (Int64.repr z0)) le)))))))
            as le_loop.
        remember 512 as num.
        set (P := fun le0 m0 => m0 = (m, d) /\ le0 = le_loop).
        set (Q := fun (le0: temp_env) m0 => m0 = (m, d) /\ le0 ! _ret = Some (Vint res)).
        set (Inv := fun le0 m0 n => exists i' ret',
                        table_maps_block_loop0 (Z.to_nat (num - n)) 0 1 (table_base, table_offset) z2
                                               (Int64.unsigned level) (Int64.unsigned ipa_state) d =
                          Some (Int.unsigned i', Int.unsigned ret') /\ Int.unsigned i' = num - n /\
                          m0 = (m, d) /\ 0 <= n /\ n <= num /\ le0 ! _i = Some (Vint i') /\
                          le0 ! _table = Some (Vptr table_base (Int.repr table_offset)) /\
                          le0 ! _level = Some (Vlong level) /\
                          le0 ! _ipa_state = Some (Vlong ipa_state) /\
                          le0 ! _ret = Some (Vint ret') /\
                          le0 ! _base_pa = Some (Vlong (Int64.repr z2))).
        assert(loop_succ: forall N, Z.of_nat N <= num -> exists i' ret',
                    table_maps_block_loop0 (Z.to_nat (num - Z.of_nat N)) 0 1
                                           (table_base, table_offset) z2
                                           (Int64.unsigned level) (Int64.unsigned ipa_state) d =
                      Some (Int.unsigned i', Int.unsigned ret')).
        { add_int Hloop z4; try somega.
          induction N. rewrite Z.sub_0_r. rewrite Hloop. intros. repeat eexists; reflexivity.
          intros. erewrite loop_ind_sub1 in IHN; try omega.
          rewrite Nat2Z.inj_succ, succ_plus_1 in H.
          assert(Hcc: Z.of_nat N <= num) by omega.
          apply IHN in Hcc. destruct Hcc as (? & ? & Hnext).
          Local Opaque Z.of_nat. simpl in Hnext. clear Heqle_loop.
          simpl_func Hnext; try add_int' z; try somega; try add_int' z1; try somega; repeat eexists. }
        assert (T: LoopProofSimpleWhile.t (external_calls_ops := CompatExternalCalls.compatlayer_extcall_ops L) cond body ge (PTree.empty _) P Q).
        { apply LoopProofSimpleWhile.make with (W:=Z) (lt:=fun z1 z2 => (0 <= z2 /\ z1 < z2)) (I:=Inv).
          - apply Zwf_well_founded.
          - unfold P, Inv. intros ? ? CC. destruct CC as [CC1 CC2].
            rewrite CC2 in *. exists num.
            replace (num - num) with 0 by omega. simpl.
            exists (Int.repr 0). exists (Int.repr 1).
            rewrite Heqnum. rewrite Heqle_loop.
            repeat eexists; first [reflexivity|assumption|solve_proof_low].
          - intros ? ? ? I. unfold Inv in I.
            destruct I as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?).
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
                rewrite H12, H13 in *; eexists; eexists; split.
                repeat big_vcgen.
                solve_func64 z1. reflexivity.
                symmetry. repeat sstep. assumption. somega.
                solve_proof_low. somega. somega. somega. somega. somega. somega.
                somega. somega. simpl.
                solve_proof_low. solve_proof_low.
                solve_proof_low. somega.
                exists (n-1); split. split; solve_proof_low.
                solve_proof_low; unfold Inv; repeat eexists; first[eassumption|solve_proof_low].
                rewrite <- (Int.repr_unsigned x2). rewrite <- H13.
                rewrite Int.repr_unsigned. assumption.

                rewrite H12, H13 in *; eexists; eexists; split.
                repeat big_vcgen.
                solve_func64 z1. reflexivity.
                symmetry. repeat sstep. assumption. somega.
                solve_proof_low. somega. somega. somega. somega. somega. somega.
                somega. somega. simpl.
                solve_proof_low. solve_proof_low.
                solve_proof_low. somega.
                exists (n-1); split. split; solve_proof_low.
                solve_proof_low; unfold Inv; repeat eexists; first[eassumption|solve_proof_low].
                rewrite H12. rewrite H13. rewrite D. sstep. reflexivity.
                rewrite H12. sstep. omega.

                rewrite H12, H13 in *; eexists; eexists; split.
                repeat big_vcgen.
                solve_func64 z1. reflexivity.
                symmetry. repeat sstep. assumption. somega.
                solve_proof_low. somega. somega. somega. somega. somega. somega.
                somega. somega. somega. somega.  simpl.
                solve_proof_low. solve_proof_low.
                solve_proof_low. somega.
                exists (n-1); split. split; solve_proof_low.
                solve_proof_low; unfold Inv; repeat eexists; first[eassumption|solve_proof_low].
                rewrite H12. rewrite H13. rewrite D. sstep. reflexivity.
                rewrite H12. sstep. omega.
            + eexists. eexists. split_and.
              * solve_proof_low.
              * solve_proof_low.
              * intro. unfold Q.
                assert (n=0) by omega. clear Heqle_loop. subst.
                sstep. rewrite Hloop in Hnow. inv Hnow.
                split_and; first[reflexivity|solve_proof_low].
              * intro CC. inversion CC. }
        assert (Pre: P le_loop (m, d)) by (split; reflexivity).
        pose proof (LoopProofSimpleWhile.termination _ _ _ _ _ _ T _ (m, d) Pre) as LoopProof.
        destruct LoopProof as (le' & m' & (exec & Post)).
        unfold exec_stmt in exec. rewrite Heqle_loop in exec.
        unfold Q in Post. destruct Post as (Post & Hle'). rewrite Post in exec.

        eexists. repeat big_vcgen.
        solve_func64 z0. reflexivity.
        symmetry. repeat sstep. assumption. somega. somega.
        solve_func64 z2. reflexivity.
        symmetry. repeat sstep.
        solve_func z3. reflexivity.
        symmetry. sstep. assumption. somega. somega. somega. somega.
        solve_proof_low. simpl.
        solve_proof_low.
      Qed.



  End BodyProof.

End CodeProof.
