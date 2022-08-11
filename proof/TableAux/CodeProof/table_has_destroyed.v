Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RunSMC.Layer.
Require Import TableAux.Code.table_has_destroyed.

Require Import TableAux.LowSpecs.table_has_destroyed.

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


  Lemma table_has_destroyed_body_correct:
      forall m d env le table_base table_offset res
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTtable: PTree.get _table le = Some (Vptr table_base (Int.repr table_offset)))
             (Hspec: table_has_destroyed_spec0 (table_base, table_offset) d = Some (Int.unsigned res)),
           exists le', (exec_stmt ge env le ((m, d): mem) table_has_destroyed_body E0 le' (m, d) (Out_return (Some (Vint res, tuint)))).
    Proof.
      solve_code_proof Hspec table_has_destroyed_body;  try solve [eexists; solve_proof_low].
      get_loop_body. clear_hyp.
      set (Hloop := C). simpl; solve_proof_low.
      remember (PTree.set _i (Vlong (Int64.repr 0)) le)  as le_loop.
      remember 512 as num.
      set (P := fun le0 m0 => m0 = (m, d) /\ le0 = le_loop).
      set (Q := fun (le0: temp_env) m0 => m0 = (m, d)).
      set (Inv := fun le0 m0 n => exists i' res',
                      table_has_destroyed_loop0 (Z.to_nat (num - n)) 0 0 (table_base, table_offset) d
                      = Some (Int64.unsigned i', Int.unsigned res') /\ Int64.unsigned i' = num - n /\
                        m0 = (m, d) /\ 0 <= n /\ n <= num /\ le0 ! _i = Some (Vlong i') /\
                        le0 ! _table = Some (Vptr table_base (Int.repr table_offset))).
      assert(loop_succ: forall N, Z.of_nat N <= num -> exists i' res',
                  table_has_destroyed_loop0 (Z.to_nat (num - Z.of_nat N)) 0 0 (table_base, table_offset) d
                  = Some (Int64.unsigned i', Int.unsigned res')).
      { add_int64 Hloop z; try somega.
        induction N. rewrite Z.sub_0_r. rewrite Hloop. intros. repeat eexists; reflexivity.
        intros. erewrite loop_ind_sub1 in IHN; try omega.
        rewrite Nat2Z.inj_succ, succ_plus_1 in H.
        assert(Hcc: Z.of_nat N <= num) by omega.
        apply IHN in Hcc. destruct Hcc as (? & ? & Hnext).
        Local Opaque Z.of_nat. simpl in Hnext. clear Heqle_loop.
        simpl_func Hnext; try add_int64' z0; try somega; try add_int' z1; try somega; repeat eexists. }
      assert (T: LoopProofSimpleWhile.t (external_calls_ops := CompatExternalCalls.compatlayer_extcall_ops L) cond body ge (PTree.empty _) P Q).
      { apply LoopProofSimpleWhile.make with (W:=Z) (lt:=fun z1 z2 => (0 <= z2 /\ z1 < z2)) (I:=Inv).
        - apply Zwf_well_founded.
        - unfold P, Inv. intros ? ? CC. destruct CC as [CC1 CC2].
          rewrite CC2 in *. exists num.
          replace (num - num) with 0 by omega. simpl.
          exists (Int64.repr 0). exists (Int.repr 0).
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
              rewrite H8, H9 in *; eexists; eexists; split.
              set (ZZ := Int64.repr z1).
              replace z1 with (Int64.unsigned ZZ) in C2.
              solve_proof_low.
              match goal with
              | [|- match ?v with Some _ => _ | None => None end = _] =>
                  replace v with (Some (VZ64 (Int64.unsigned ZZ)))
              end.
              reflexivity.
              somega. replace ZZ with (Int64.repr z1) by reflexivity.
              solve_proof_low.
              exists (n-1); split. split; solve_proof_low.
              solve_proof_low; unfold Inv; repeat eexists; first[eassumption|solve_proof_low].
              rewrite H8, H9. rewrite D. solve_proof_low.
              rewrite H8. solve_proof_low.

              rewrite H8, H9 in *; eexists; eexists; split.
              set (ZZ := Int64.repr z1).
              replace z1 with (Int64.unsigned ZZ) in C2.
              solve_proof_low.
              match goal with
              | [|- match ?v with Some _ => _ | None => None end = _] =>
                  replace v with (Some (VZ64 (Int64.unsigned ZZ)))
              end.
              reflexivity.
              somega. somega. somega.
              replace ZZ with (Int64.repr z1) by reflexivity.
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
        assert (Pre: P le_loop (m, d)) by (split; reflexivity).
        pose proof (LoopProofSimpleWhile.termination _ _ _ _ _ _ T _ (m, d) Pre) as LoopProof.
        destruct LoopProof as (le' & m' & (exec & Post)).
        unfold exec_stmt in exec. rewrite Heqle_loop in exec.
        unfold Q in Post. rewrite Post in exec.
        eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
