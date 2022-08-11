Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import PSCIAux.Spec.
Require Import PSCIAux.Layer.
Require Import PSCIAux2.Code.system_off_reboot.

Require Import PSCIAux2.LowSpecs.system_off_reboot.

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
    _get_rec_g_rec ↦ gensem get_rec_g_rec_spec
      ⊕ _get_rec_g_rd ↦ gensem get_rec_g_rd_spec
      ⊕ _get_rec_rec_idx ↦ gensem get_rec_rec_idx_spec
      ⊕ _get_rec_g_rec_list ↦ gensem get_rec_g_rec_list_spec
      ⊕ _granule_lock ↦ gensem granule_lock_spec
      ⊕ _set_rec_runnable ↦ gensem set_rec_runnable_spec
      ⊕ _granule_unlock ↦ gensem granule_unlock_spec
      ⊕ _granule_map ↦ gensem granule_map_spec
      ⊕ _find_lock_rec ↦ gensem find_lock_rec_spec
      ⊕ _is_null ↦ gensem is_null_spec
      ⊕ _buffer_unmap ↦ gensem buffer_unmap_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_get_rec_g_rec: block.
    Hypothesis h_get_rec_g_rec_s : Genv.find_symbol ge _get_rec_g_rec = Some b_get_rec_g_rec.
    Hypothesis h_get_rec_g_rec_p : Genv.find_funct_ptr ge b_get_rec_g_rec
                                   = Some (External (EF_external _get_rec_g_rec
                                                    (signature_of_type (Tcons Tptr Tnil) Tptr cc_default))
                                          (Tcons Tptr Tnil) Tptr cc_default).
    Local Opaque get_rec_g_rec_spec.

    Variable b_get_rec_g_rd: block.
    Hypothesis h_get_rec_g_rd_s : Genv.find_symbol ge _get_rec_g_rd = Some b_get_rec_g_rd.
    Hypothesis h_get_rec_g_rd_p : Genv.find_funct_ptr ge b_get_rec_g_rd
                                  = Some (External (EF_external _get_rec_g_rd
                                                   (signature_of_type (Tcons Tptr Tnil) Tptr cc_default))
                                         (Tcons Tptr Tnil) Tptr cc_default).
    Local Opaque get_rec_g_rd_spec.

    Variable b_get_rec_rec_idx: block.
    Hypothesis h_get_rec_rec_idx_s : Genv.find_symbol ge _get_rec_rec_idx = Some b_get_rec_rec_idx.
    Hypothesis h_get_rec_rec_idx_p : Genv.find_funct_ptr ge b_get_rec_rec_idx
                                     = Some (External (EF_external _get_rec_rec_idx
                                                      (signature_of_type (Tcons Tptr Tnil) tulong cc_default))
                                            (Tcons Tptr Tnil) tulong cc_default).
    Local Opaque get_rec_rec_idx_spec.

    Variable b_get_rec_g_rec_list: block.
    Hypothesis h_get_rec_g_rec_list_s : Genv.find_symbol ge _get_rec_g_rec_list = Some b_get_rec_g_rec_list.
    Hypothesis h_get_rec_g_rec_list_p : Genv.find_funct_ptr ge b_get_rec_g_rec_list
                                        = Some (External (EF_external _get_rec_g_rec_list
                                                         (signature_of_type (Tcons Tptr Tnil) Tptr cc_default))
                                               (Tcons Tptr Tnil) Tptr cc_default).
    Local Opaque get_rec_g_rec_list_spec.

    Variable b_granule_lock: block.
    Hypothesis h_granule_lock_s : Genv.find_symbol ge _granule_lock = Some b_granule_lock.
    Hypothesis h_granule_lock_p : Genv.find_funct_ptr ge b_granule_lock
                                  = Some (External (EF_external _granule_lock
                                                   (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                         (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque granule_lock_spec.

    Variable b_set_rec_runnable: block.
    Hypothesis h_set_rec_runnable_s : Genv.find_symbol ge _set_rec_runnable = Some b_set_rec_runnable.
    Hypothesis h_set_rec_runnable_p : Genv.find_funct_ptr ge b_set_rec_runnable
                                      = Some (External (EF_external _set_rec_runnable
                                                       (signature_of_type (Tcons Tptr (Tcons tuint Tnil)) tvoid cc_default))
                                             (Tcons Tptr (Tcons tuint Tnil)) tvoid cc_default).
    Local Opaque set_rec_runnable_spec.

    Variable b_granule_unlock: block.
    Hypothesis h_granule_unlock_s : Genv.find_symbol ge _granule_unlock = Some b_granule_unlock.
    Hypothesis h_granule_unlock_p : Genv.find_funct_ptr ge b_granule_unlock
                                    = Some (External (EF_external _granule_unlock
                                                     (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                           (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque granule_unlock_spec.

    Variable b_granule_map: block.
    Hypothesis h_granule_map_s : Genv.find_symbol ge _granule_map = Some b_granule_map.
    Hypothesis h_granule_map_p : Genv.find_funct_ptr ge b_granule_map
                                 = Some (External (EF_external _granule_map
                                                  (signature_of_type (Tcons Tptr (Tcons tuint Tnil)) Tptr cc_default))
                                        (Tcons Tptr (Tcons tuint Tnil)) Tptr cc_default).
    Local Opaque granule_map_spec.

    Variable b_find_lock_rec: block.
    Hypothesis h_find_lock_rec_s : Genv.find_symbol ge _find_lock_rec = Some b_find_lock_rec.
    Hypothesis h_find_lock_rec_p : Genv.find_funct_ptr ge b_find_lock_rec
                                   = Some (External (EF_external _find_lock_rec
                                                    (signature_of_type (Tcons Tptr (Tcons Tptr (Tcons tulong Tnil))) Tptr cc_default))
                                          (Tcons Tptr (Tcons Tptr (Tcons tulong Tnil))) Tptr cc_default).
    Local Opaque find_lock_rec_spec.

    Variable b_is_null: block.
    Hypothesis h_is_null_s : Genv.find_symbol ge _is_null = Some b_is_null.
    Hypothesis h_is_null_p : Genv.find_funct_ptr ge b_is_null
                             = Some (External (EF_external _is_null
                                              (signature_of_type (Tcons Tptr Tnil) tuint cc_default))
                                    (Tcons Tptr Tnil) tuint cc_default).
    Local Opaque is_null_spec.

    Variable b_buffer_unmap: block.
    Hypothesis h_buffer_unmap_s : Genv.find_symbol ge _buffer_unmap = Some b_buffer_unmap.
    Hypothesis h_buffer_unmap_p : Genv.find_funct_ptr ge b_buffer_unmap
                                  = Some (External (EF_external _buffer_unmap
                                                   (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                         (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque buffer_unmap_spec.


    Lemma system_off_reboot_body_correct:
      forall m d d' env le rec_base rec_offset
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTrec: PTree.get _rec le = Some (Vptr rec_base (Int.repr rec_offset)))
             (Hspec: system_off_reboot_spec0 (rec_base, rec_offset) d = Some d'),
           exists le', (exec_stmt ge env le ((m, d): mem) system_off_reboot_body E0 le' (m, d') Out_normal).
    Proof.
      solve_code_proof Hspec system_off_reboot_body.
      destruct p, p0, p1, p3.
      add_int64 C1 z0; try somega.
      remember (Int64.repr z0) as ZZ.

      get_loop_body. clear_hyp.
      set (Hloop := C10). simpl; solve_proof_low.
      remember
        (PTree.set _i (Vlong (Int64.repr 0))
            (PTree.set _rec_list (Vptr p2 (Int.repr z4))
              (PTree.set _t'5 (Vptr p2 (Int.repr z4))
                  (PTree.set _g (Vptr p1 (Int.repr z3))
                    (PTree.set _t'4 (Vptr p1 (Int.repr z3))
                        (PTree.set _idx (Vlong ZZ)
                          (PTree.set _t'3 (Vlong ZZ)
                              (PTree.set _g_rd (Vptr p0 (Int.repr z2))
                                (PTree.set _t'2 (Vptr p0 (Int.repr z2))
                                    (PTree.set _g_rec (Vptr p (Int.repr z))
                                      (PTree.set _t'1 (Vptr p (Int.repr z)) le))))))))))) as le_loop.
      remember 512 as num.
      set (P := fun le0 m0 => m0 = (m, r2) /\ le0 = le_loop).
      set (Q := fun (le0: temp_env) m0 => m0 = (m, r3) /\ le0 ! _rec_list = Some (Vptr p2 (Int.repr z4))).
      set (Inv := fun le0 m0 n => exists i' adt',
                      system_off_reboot_loop0 (Z.to_nat (num - n)) 0 z0 (p0, z2) (p2, z4) r2 =
                        Some (adt', Int64.unsigned i') /\ Int64.unsigned i' = num - n /\
                        m0 = (m, adt') /\ 0 <= n /\ n <= num /\ le0 ! _i = Some (Vlong i') /\
                        le0 ! _g_rd = Some (Vptr p0 (Int.repr z2)) /\
                        le0 ! _rec_list = Some (Vptr p2 (Int.repr z4)) /\
                        le0 ! _idx = Some (Vlong (Int64.repr z0))).
      assert(loop_succ: forall N, Z.of_nat N <= num -> exists i' adt',
                  system_off_reboot_loop0 (Z.to_nat (num - Z.of_nat N)) 0 z0 (p0, z2) (p2, z4) r2 =
                    Some (adt', Int64.unsigned i')).
      { add_int64 Hloop z1; try somega.
        induction N. rewrite Z.sub_0_r. rewrite Hloop. intros. repeat eexists; reflexivity.
        intros. erewrite loop_ind_sub1 in IHN; try omega.
        rewrite Nat2Z.inj_succ, succ_plus_1 in H.
        assert(Hcc: Z.of_nat N <= num) by omega.
        apply IHN in Hcc. destruct Hcc as (? & ? & Hnext).
        Local Opaque Z.of_nat. simpl in Hnext. clear Heqle_loop.
        simpl_func Hnext; try add_int64' z5; try somega; repeat eexists. }
      assert (T: LoopProofSimpleWhile.t (external_calls_ops := CompatExternalCalls.compatlayer_extcall_ops L) cond body ge (PTree.empty _) P Q).
      { apply LoopProofSimpleWhile.make with (W:=Z) (lt:=fun z1 z2 => (0 <= z2 /\ z1 < z2)) (I:=Inv).
        - apply Zwf_well_founded.
        - unfold P, Inv. intros ? ? CC. destruct CC as [CC1 CC2].
          rewrite CC2 in *. exists num.
          replace (num - num) with 0 by omega. simpl.
          exists (Int64.repr 0). exists r2.
          rewrite Heqnum. rewrite Heqle_loop. rewrite HeqZZ.
          repeat eexists; first [reflexivity|assumption|solve_proof_low].
        - intros ? ? ? I. unfold Inv in I. destruct I as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?).
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
              rewrite H11, H12 in *; eexists; eexists; split.
              solve_proof_low.
              exists (n-1); split. split; solve_proof_low.
              solve_proof_low; unfold Inv; repeat eexists; first[eassumption|solve_proof_low].

              destruct p4, p6.
              rewrite H11, H12 in *; eexists; eexists; split.
              solve_proof_low.
              exists (n-1); split. split; solve_proof_low.
              solve_proof_low; unfold Inv; repeat eexists; first[eassumption|solve_proof_low].

              destruct p4.
              rewrite H11, H12 in *; eexists; eexists; split.
              solve_proof_low.
              exists (n-1); split. split; solve_proof_low.
              solve_proof_low; unfold Inv; repeat eexists; first[eassumption|solve_proof_low].
          + eexists. eexists. split_and.
            * solve_proof_low.
            * solve_proof_low.
            * intro. unfold Q.
              assert (n=0) by omega. clear Heqle_loop. subst.
              sstep. rewrite Hloop in Hnow. inv Hnow.
              split_and; first[reflexivity|solve_proof_low].
              somega.
            * intro CC. inversion CC. }
        assert (Pre: P le_loop (m, r2)) by (split; reflexivity).
        pose proof (LoopProofSimpleWhile.termination _ _ _ _ _ _ T _ (m, r2) Pre) as LoopProof.
        destruct LoopProof as (le' & m' & (exec & Post)).
        unfold exec_stmt in exec. rewrite Heqle_loop in exec.
        unfold Q in Post. destruct Post as (Post & Hle'). rewrite Post in exec.
        eexists; solve_proof_low.

      match goal with
      | [|- match ?v with Some _ => _ | None => None end = _] =>
          replace v with (Some (VZ64 (Int64.unsigned ZZ)))
      end.
      reflexivity.
    Qed.

  End BodyProof.

End CodeProof.
