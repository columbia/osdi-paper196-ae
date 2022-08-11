Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import TableAux.Spec.
Require Import TableAux2.Layer.
Require Import TableWalk.Code.table_walk_lock_unlock.

Require Import TableWalk.LowSpecs.table_walk_lock_unlock.

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
    _granule_map ↦ gensem granule_map_spec
      ⊕ _get_rd_g_rtt ↦ gensem get_rd_g_rtt_spec
      ⊕ _buffer_unmap ↦ gensem buffer_unmap_spec
      ⊕ _granule_lock ↦ gensem granule_lock_spec
      ⊕ _is_null ↦ gensem is_null_spec
      ⊕ _addr_to_idx ↦ gensem addr_to_idx_spec
      ⊕ _find_next_level_idx ↦ gensem find_next_level_idx_spec
      ⊕ _granule_unlock ↦ gensem granule_unlock_spec
      ⊕ _set_wi_g_llt ↦ gensem set_wi_g_llt_spec
      ⊕ _set_wi_index ↦ gensem set_wi_index_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_granule_map: block.
    Hypothesis h_granule_map_s : Genv.find_symbol ge _granule_map = Some b_granule_map.
    Hypothesis h_granule_map_p : Genv.find_funct_ptr ge b_granule_map
                                 = Some (External (EF_external _granule_map
                                                  (signature_of_type (Tcons Tptr (Tcons tuint Tnil)) Tptr cc_default))
                                        (Tcons Tptr (Tcons tuint Tnil)) Tptr cc_default).
    Local Opaque granule_map_spec.

    Variable b_get_rd_g_rtt: block.
    Hypothesis h_get_rd_g_rtt_s : Genv.find_symbol ge _get_rd_g_rtt = Some b_get_rd_g_rtt.
    Hypothesis h_get_rd_g_rtt_p : Genv.find_funct_ptr ge b_get_rd_g_rtt
                                  = Some (External (EF_external _get_rd_g_rtt
                                                   (signature_of_type (Tcons Tptr Tnil) Tptr cc_default))
                                         (Tcons Tptr Tnil) Tptr cc_default).
    Local Opaque get_rd_g_rtt_spec.

    Variable b_buffer_unmap: block.
    Hypothesis h_buffer_unmap_s : Genv.find_symbol ge _buffer_unmap = Some b_buffer_unmap.
    Hypothesis h_buffer_unmap_p : Genv.find_funct_ptr ge b_buffer_unmap
                                  = Some (External (EF_external _buffer_unmap
                                                   (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                         (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque buffer_unmap_spec.

    Variable b_granule_lock: block.
    Hypothesis h_granule_lock_s : Genv.find_symbol ge _granule_lock = Some b_granule_lock.
    Hypothesis h_granule_lock_p : Genv.find_funct_ptr ge b_granule_lock
                                  = Some (External (EF_external _granule_lock
                                                   (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                         (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque granule_lock_spec.

    Variable b_is_null: block.
    Hypothesis h_is_null_s : Genv.find_symbol ge _is_null = Some b_is_null.
    Hypothesis h_is_null_p : Genv.find_funct_ptr ge b_is_null
                             = Some (External (EF_external _is_null
                                              (signature_of_type (Tcons Tptr Tnil) tuint cc_default))
                                    (Tcons Tptr Tnil) tuint cc_default).
    Local Opaque is_null_spec.

    Variable b_addr_to_idx: block.
    Hypothesis h_addr_to_idx_s : Genv.find_symbol ge _addr_to_idx = Some b_addr_to_idx.
    Hypothesis h_addr_to_idx_p : Genv.find_funct_ptr ge b_addr_to_idx
                                 = Some (External (EF_external _addr_to_idx
                                                  (signature_of_type (Tcons tulong (Tcons tulong Tnil)) tulong cc_default))
                                        (Tcons tulong (Tcons tulong Tnil)) tulong cc_default).
    Local Opaque addr_to_idx_spec.

    Variable b_find_next_level_idx: block.
    Hypothesis h_find_next_level_idx_s : Genv.find_symbol ge _find_next_level_idx = Some b_find_next_level_idx.
    Hypothesis h_find_next_level_idx_p : Genv.find_funct_ptr ge b_find_next_level_idx
                                         = Some (External (EF_external _find_next_level_idx
                                                          (signature_of_type (Tcons Tptr (Tcons tulong Tnil)) Tptr cc_default))
                                                (Tcons Tptr (Tcons tulong Tnil)) Tptr cc_default).
    Local Opaque find_next_level_idx_spec.

    Variable b_granule_unlock: block.
    Hypothesis h_granule_unlock_s : Genv.find_symbol ge _granule_unlock = Some b_granule_unlock.
    Hypothesis h_granule_unlock_p : Genv.find_funct_ptr ge b_granule_unlock
                                    = Some (External (EF_external _granule_unlock
                                                     (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                           (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque granule_unlock_spec.

    Variable b_set_wi_g_llt: block.
    Hypothesis h_set_wi_g_llt_s : Genv.find_symbol ge _set_wi_g_llt = Some b_set_wi_g_llt.
    Hypothesis h_set_wi_g_llt_p : Genv.find_funct_ptr ge b_set_wi_g_llt
                                  = Some (External (EF_external _set_wi_g_llt
                                                   (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                         (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque set_wi_g_llt_spec.

    Variable b_set_wi_index: block.
    Hypothesis h_set_wi_index_s : Genv.find_symbol ge _set_wi_index = Some b_set_wi_index.
    Hypothesis h_set_wi_index_p : Genv.find_funct_ptr ge b_set_wi_index
                                  = Some (External (EF_external _set_wi_index
                                                   (signature_of_type (Tcons tulong Tnil) tvoid cc_default))
                                         (Tcons tulong Tnil) tvoid cc_default).
    Local Opaque set_wi_index_spec.

  Fixpoint table_walk_lock_unlock_loop0 (n: nat) (l: Z) (tbl: Pointer) (last_tbl: Pointer) (map_addr: Z) (adt: RData) :=
    match n with
    | O => Some (l, tbl, last_tbl, adt)
    | S n' =>
      match table_walk_lock_unlock_loop0 n' l tbl last_tbl map_addr adt with
      | Some (l, (tbl_base, tbl_ofst), (last_tbl_base, last_tbl_ofst), adt) =>
        rely is_int l; rely is_int tbl_ofst; rely is_int last_tbl_ofst;
        when null == is_null_spec (tbl_base, tbl_ofst) adt;
        rely is_int null;
        if null =? 0 then
          when' idx == addr_to_idx_spec (VZ64 map_addr) (VZ64 l) adt;
          rely is_int64 idx;
          when'' tbl_base, tbl_ofst, adt == find_next_level_idx_spec (tbl_base, tbl_ofst) (VZ64 idx) adt;
          rely is_int tbl_ofst;
          when null == is_null_spec (tbl_base, tbl_ofst) adt;
          rely is_int null;
          if null =? 0 then
            when adt == granule_lock_spec (tbl_base, tbl_ofst) adt;
            when adt == granule_unlock_spec (last_tbl_base, last_tbl_ofst) adt;
            Some (l + 1, (tbl_base, tbl_ofst), (tbl_base, tbl_ofst), adt)
          else
            when adt == granule_unlock_spec (last_tbl_base, last_tbl_ofst) adt;
            Some (l + 1, (tbl_base, tbl_ofst), (last_tbl_base, last_tbl_ofst), adt)
        else Some (l + 1, (tbl_base, tbl_ofst), (last_tbl_base, last_tbl_ofst), adt)
      | _ => None
      end
    end.

  Definition table_walk_lock_unlock_spec0 (g_rd: Pointer) (map_addr: Z64) (level: Z64) (adt: RData) : option RData :=
    match map_addr, level with
    | VZ64 map_addr, VZ64 level =>
      when'' rd_base, rd_ofst, adt == granule_map_spec g_rd SLOT_RD adt;
      rely is_int rd_ofst;
      when'' g_root_base, g_root_ofst == get_rd_g_rtt_spec (rd_base, rd_ofst) adt;
      rely is_int g_root_ofst;
      when adt == buffer_unmap_spec (rd_base, rd_ofst) adt;
      when adt == granule_lock_spec (g_root_base, g_root_ofst) adt;
      match table_walk_lock_unlock_loop0 (Z.to_nat level) 0 (g_root_base, g_root_ofst) (g_root_base, g_root_ofst) map_addr adt with
      | Some (l, (tbl_base, tbl_ofst), (last_tbl_base, last_tbl_ofst), adt) =>
        rely is_int l; rely is_int tbl_ofst; rely is_int last_tbl_ofst;
        when adt == set_wi_g_llt_spec (tbl_base, tbl_ofst) adt;
        when' idx == addr_to_idx_spec (VZ64 map_addr) (VZ64 level) adt;
        rely is_int64 idx;
        when adt == set_wi_index_spec (VZ64 idx) adt;
        Some adt
      | _ => None
      end
    end.

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

    Lemma table_walk_lock_unlock_body_correct:
      forall m d d' env le g_rd_base g_rd_offset map_addr level
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTg_rd: PTree.get _g_rd le = Some (Vptr g_rd_base (Int.repr g_rd_offset)))
             (HPTmap_addr: PTree.get _map_addr le = Some (Vlong map_addr))
             (HPTlevel: PTree.get _level le = Some (Vlong level))
             (Hspec: table_walk_lock_unlock_spec0 (g_rd_base, g_rd_offset) (VZ64 (Int64.unsigned map_addr)) (VZ64 (Int64.unsigned level)) d = Some d'),
           exists le', (exec_stmt ge env le ((m, d): mem) table_walk_lock_unlock_body E0 le' (m, d') Out_normal).
    Proof.
      solve_code_proof Hspec table_walk_lock_unlock_body.
      get_loop_body. clear_hyp.
      set (Hloop := C8). simpl; solve_proof_low.
      remember
        (PTree.set _last_tbl (Vptr p3 (Int.repr z0))
            (PTree.set _tbl (Vptr p3 (Int.repr z0))
              (PTree.set _t'3 (Vptr p3 (Int.repr z0))
                  (PTree.set _g_root (Vptr p3 (Int.repr z0))
                    (PTree.set _t'2 (Vptr p3 (Int.repr z0))
                        (PTree.set _rd (Vptr p1 (Int.repr z))
                          (PTree.set _t'1 (Vptr p1 (Int.repr z))
                              (PTree.set _last_level (Vlong (Int64.repr 0))
                                (PTree.set _l (Vlong (Int64.repr 0)) le)))))))))
            as le_loop.
      remember (Int64.unsigned level) as num.
      set (P := fun le0 m0 => m0 = (m, r1) /\ le0 = le_loop).
      set (Q := fun (le0: temp_env) m0 => m0 = (m, r2) /\
                                            le0 ! _map_addr = Some (Vlong map_addr) /\
                                            le0 ! _level = Some (Vlong level) /\
                                            le0 ! _tbl = Some (Vptr p9 (Int.repr z2))).
      set (Inv := fun le0 m0 n => exists l' tbl_base' tbl_ofst' last_tbl_base' last_tbl_ofst' adt',
                      table_walk_lock_unlock_loop0 (Z.to_nat (num - n)) 0
                                                   (p3, z0) (p3, z0) (Int64.unsigned map_addr) r1 =
                        Some (Int64.unsigned l', (tbl_base', tbl_ofst'),
                               (last_tbl_base', last_tbl_ofst'), adt') /\
                        Int64.unsigned l' = num - n /\
                        m0 = (m, adt') /\ 0 <= n /\ n <= num /\
                        le0 ! _l = Some (Vlong l') /\
                        le0 ! _map_addr = Some (Vlong map_addr) /\
                        le0 ! _level = Some (Vlong level) /\
                        le0 ! _tbl = Some (Vptr tbl_base' (Int.repr tbl_ofst')) /\
                        le0 ! _last_tbl = Some (Vptr last_tbl_base' (Int.repr last_tbl_ofst'))).
      assert(loop_succ: forall N, Z.of_nat N <= num -> exists l' tbl_base' tbl_ofst' last_tbl_base' last_tbl_ofst' adt',
                  table_walk_lock_unlock_loop0 (Z.to_nat (num - Z.of_nat N)) 0
                                               (p3, z0) (p3, z0) (Int64.unsigned map_addr) r1 =
                    Some (Int64.unsigned l', (tbl_base', tbl_ofst'),
                           (last_tbl_base', last_tbl_ofst'), adt')).
        { add_int64 Hloop z1; try somega.
          add_int Hloop z2; try somega.
          add_int Hloop z3; try somega.
          induction N. rewrite Z.sub_0_r. rewrite Hloop. intros. repeat eexists; reflexivity.
          intros. erewrite loop_ind_sub1 in IHN; try omega.
          rewrite Nat2Z.inj_succ, succ_plus_1 in H.
          assert(Hcc: Z.of_nat N <= num) by omega.
          apply IHN in Hcc. destruct Hcc as (? & ? & ? & ? & ? & ? & Hnext).
          Local Opaque Z.of_nat. simpl in Hnext. clear Heqle_loop.
          simpl_func Hnext;
            try add_int64' z4; try somega; try add_int' z6; try somega;
            try add_int' z7; try somega; repeat eexists. }
        assert (T: LoopProofSimpleWhile.t (external_calls_ops := CompatExternalCalls.compatlayer_extcall_ops L) cond body ge (PTree.empty _) P Q).
        { apply LoopProofSimpleWhile.make with (W:=Z) (lt:=fun z1 z2 => (0 <= z2 /\ z1 < z2)) (I:=Inv).
          - apply Zwf_well_founded.
          - unfold P, Inv. intros ? ? CC. destruct CC as [CC1 CC2].
            rewrite CC2 in *. exists num.
            replace (num - num) with 0 by omega. simpl.
            exists (Int64.repr 0). eexists. eexists.
            eexists. eexists. eexists.
            rewrite Heqnum. rewrite Heqle_loop.
            repeat eexists; first [reflexivity|assumption|solve_proof_low].
          - intros ? ? ? I. unfold Inv in I.
            destruct I as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?).
            set (Hnow := H).
            rewrite Heqbody, Heqcond in *.
            destruct (n >? 0) eqn:Hn; bool_rel.
            + eexists. eexists. split_and.
              * solve_proof_low.
              * solve_proof_low.
              * intro CC. inversion CC.
              * assert(Hlx: Z.of_nat (Z.to_nat (n-1)) <= num) by (rewrite Z2Nat.id; omega).
                apply loop_succ in Hlx. rewrite Z2Nat.id in Hlx; try omega.
                intro. destruct Hlx as (? & ? & ? & ? & ? & ? & Hnext). duplicate Hnext.
                rewrite loop_nat_sub1 in Hnext; try somega.
                simpl in Hnext. rewrite Hnow in Hnext.
                autounfold in Hnext; repeat simpl_hyp Hnext;
                  repeat destruct_con; bool_rel; contra; inversion Hnext.
                rewrite H12 in *. rewrite H13 in *. rewrite H14 in *.
                rewrite H15 in *. rewrite H16 in *.
                 eexists; eexists; split.
                repeat big_vcgen. solve_func z4. reflexivity.
                symmetry. sstep. assumption. somega.
                solve_proof_low. simpl.
                solve_proof_low. solve_proof_low.
                solve_proof_low.
                exists (n-1); split. split; solve_proof_low.
                solve_proof_low; unfold Inv; repeat eexists; first[eassumption|solve_proof_low].

                rewrite H12 in *. rewrite H13 in *. rewrite H14 in *.
                rewrite H15 in *. rewrite H16 in *.
                eexists; eexists; split.
                repeat big_vcgen. solve_func z4. reflexivity.
                symmetry. sstep. assumption. somega.
                solve_proof_low. simpl.
                solve_proof_low. solve_proof_low.
                solve_proof_low.
                exists (n-1); split. split; solve_proof_low.
                solve_proof_low; unfold Inv; repeat eexists; first[eassumption|solve_proof_low].

                rewrite H12 in *. rewrite H13 in *. rewrite H14 in *.
                rewrite H15 in *. rewrite H16 in *.
                eexists; eexists; split.
                repeat big_vcgen. solve_func z4. reflexivity.
                symmetry. sstep. assumption. somega.
                solve_proof_low. simpl.
                solve_proof_low. solve_proof_low.
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
              * intro CC. inversion CC. }
        assert (Pre: P le_loop (m, r1)) by (split; reflexivity).
        pose proof (LoopProofSimpleWhile.termination _ _ _ _ _ _ T _ (m, r1) Pre) as LoopProof.
        destruct LoopProof as (le' & m' & (exec & Post)).
        unfold exec_stmt in exec. rewrite Heqle_loop in exec.
        unfold Q in Post. destruct Post as (Post & Hle'). rewrite Post in exec.

      destruct Hle' as (? & ? & ?).
      eexists; solve_proof_low.
      solve_func64 z5. reflexivity.
      symmetry. sstep. rewrite <- Heqnum. assumption.
      sstep. sstep. assumption. somega.
    Qed.

  End BodyProof.

End CodeProof.
