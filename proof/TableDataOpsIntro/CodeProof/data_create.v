Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import TableWalk.Spec.
Require Import AbsAccessor.Spec.
Require Import TableWalk.Layer.
Require Import TableDataOpsIntro.Code.data_create.

Require Import TableDataOpsIntro.LowSpecs.data_create.

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
    _table_walk_lock_unlock ↦ gensem table_walk_lock_unlock_spec
      ⊕ _get_wi_g_llt ↦ gensem get_wi_g_llt_spec
      ⊕ _get_wi_index ↦ gensem get_wi_index_spec
      ⊕ _is_null ↦ gensem is_null_spec
      ⊕ _granule_map ↦ gensem granule_map_spec
      ⊕ _pgte_read ↦ gensem pgte_read_spec
      ⊕ _ns_granule_map ↦ gensem ns_granule_map_spec
      ⊕ _ns_buffer_read_data ↦ gensem ns_buffer_read_data_spec
      ⊕ _ns_buffer_unmap ↦ gensem ns_buffer_unmap_spec
      ⊕ _buffer_unmap ↦ gensem buffer_unmap_spec
      ⊕ _granule_memzero_mapped ↦ gensem granule_memzero_mapped_spec
      ⊕ _granule_memzero ↦ gensem granule_memzero_spec
      ⊕ _pgte_write ↦ gensem pgte_write_spec
      ⊕ _set_mapping ↦ gensem set_mapping_spec
      ⊕ _granule_get ↦ gensem granule_get_spec
      ⊕ _granule_unlock ↦ gensem granule_unlock_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_table_walk_lock_unlock: block.
    Hypothesis h_table_walk_lock_unlock_s : Genv.find_symbol ge _table_walk_lock_unlock = Some b_table_walk_lock_unlock.
    Hypothesis h_table_walk_lock_unlock_p : Genv.find_funct_ptr ge b_table_walk_lock_unlock
                                            = Some (External (EF_external _table_walk_lock_unlock
                                                             (signature_of_type (Tcons Tptr (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default))
                                                   (Tcons Tptr (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default).
    Local Opaque table_walk_lock_unlock_spec.

    Variable b_get_wi_g_llt: block.
    Hypothesis h_get_wi_g_llt_s : Genv.find_symbol ge _get_wi_g_llt = Some b_get_wi_g_llt.
    Hypothesis h_get_wi_g_llt_p : Genv.find_funct_ptr ge b_get_wi_g_llt
                                  = Some (External (EF_external _get_wi_g_llt
                                                   (signature_of_type Tnil Tptr cc_default))
                                         Tnil Tptr cc_default).
    Local Opaque get_wi_g_llt_spec.

    Variable b_get_wi_index: block.
    Hypothesis h_get_wi_index_s : Genv.find_symbol ge _get_wi_index = Some b_get_wi_index.
    Hypothesis h_get_wi_index_p : Genv.find_funct_ptr ge b_get_wi_index
                                  = Some (External (EF_external _get_wi_index
                                                   (signature_of_type Tnil tulong cc_default))
                                         Tnil tulong cc_default).
    Local Opaque get_wi_index_spec.

    Variable b_is_null: block.
    Hypothesis h_is_null_s : Genv.find_symbol ge _is_null = Some b_is_null.
    Hypothesis h_is_null_p : Genv.find_funct_ptr ge b_is_null
                             = Some (External (EF_external _is_null
                                              (signature_of_type (Tcons Tptr Tnil) tuint cc_default))
                                    (Tcons Tptr Tnil) tuint cc_default).
    Local Opaque is_null_spec.

    Variable b_granule_map: block.
    Hypothesis h_granule_map_s : Genv.find_symbol ge _granule_map = Some b_granule_map.
    Hypothesis h_granule_map_p : Genv.find_funct_ptr ge b_granule_map
                                 = Some (External (EF_external _granule_map
                                                  (signature_of_type (Tcons Tptr (Tcons tuint Tnil)) Tptr cc_default))
                                        (Tcons Tptr (Tcons tuint Tnil)) Tptr cc_default).
    Local Opaque granule_map_spec.

    Variable b_pgte_read: block.
    Hypothesis h_pgte_read_s : Genv.find_symbol ge _pgte_read = Some b_pgte_read.
    Hypothesis h_pgte_read_p : Genv.find_funct_ptr ge b_pgte_read
                               = Some (External (EF_external _pgte_read
                                                (signature_of_type (Tcons Tptr (Tcons tulong Tnil)) tulong cc_default))
                                      (Tcons Tptr (Tcons tulong Tnil)) tulong cc_default).
    Local Opaque pgte_read_spec.

    Variable b_ns_granule_map: block.
    Hypothesis h_ns_granule_map_s : Genv.find_symbol ge _ns_granule_map = Some b_ns_granule_map.
    Hypothesis h_ns_granule_map_p : Genv.find_funct_ptr ge b_ns_granule_map
                                    = Some (External (EF_external _ns_granule_map
                                                     (signature_of_type (Tcons tuint (Tcons Tptr Tnil)) tvoid cc_default))
                                           (Tcons tuint (Tcons Tptr Tnil)) tvoid cc_default).
    Local Opaque ns_granule_map_spec.

    Variable b_ns_buffer_read_data: block.
    Hypothesis h_ns_buffer_read_data_s : Genv.find_symbol ge _ns_buffer_read_data = Some b_ns_buffer_read_data.
    Hypothesis h_ns_buffer_read_data_p : Genv.find_funct_ptr ge b_ns_buffer_read_data
                                         = Some (External (EF_external _ns_buffer_read_data
                                                          (signature_of_type (Tcons tuint (Tcons Tptr Tnil)) tuint cc_default))
                                                (Tcons tuint (Tcons Tptr Tnil)) tuint cc_default).
    Local Opaque ns_buffer_read_data_spec.

    Variable b_ns_buffer_unmap: block.
    Hypothesis h_ns_buffer_unmap_s : Genv.find_symbol ge _ns_buffer_unmap = Some b_ns_buffer_unmap.
    Hypothesis h_ns_buffer_unmap_p : Genv.find_funct_ptr ge b_ns_buffer_unmap
                                     = Some (External (EF_external _ns_buffer_unmap
                                                      (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                            (Tcons tuint Tnil) tvoid cc_default).
    Local Opaque ns_buffer_unmap_spec.

    Variable b_buffer_unmap: block.
    Hypothesis h_buffer_unmap_s : Genv.find_symbol ge _buffer_unmap = Some b_buffer_unmap.
    Hypothesis h_buffer_unmap_p : Genv.find_funct_ptr ge b_buffer_unmap
                                  = Some (External (EF_external _buffer_unmap
                                                   (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                         (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque buffer_unmap_spec.

    Variable b_granule_memzero_mapped: block.
    Hypothesis h_granule_memzero_mapped_s : Genv.find_symbol ge _granule_memzero_mapped = Some b_granule_memzero_mapped.
    Hypothesis h_granule_memzero_mapped_p : Genv.find_funct_ptr ge b_granule_memzero_mapped
                                            = Some (External (EF_external _granule_memzero_mapped
                                                             (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                                   (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque granule_memzero_mapped_spec.

    Variable b_granule_memzero: block.
    Hypothesis h_granule_memzero_s : Genv.find_symbol ge _granule_memzero = Some b_granule_memzero.
    Hypothesis h_granule_memzero_p : Genv.find_funct_ptr ge b_granule_memzero
                                     = Some (External (EF_external _granule_memzero
                                                      (signature_of_type (Tcons Tptr (Tcons tuint Tnil)) tvoid cc_default))
                                            (Tcons Tptr (Tcons tuint Tnil)) tvoid cc_default).
    Local Opaque granule_memzero_spec.

    Variable b_pgte_write: block.
    Hypothesis h_pgte_write_s : Genv.find_symbol ge _pgte_write = Some b_pgte_write.
    Hypothesis h_pgte_write_p : Genv.find_funct_ptr ge b_pgte_write
                                = Some (External (EF_external _pgte_write
                                                 (signature_of_type (Tcons Tptr (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default))
                                       (Tcons Tptr (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default).
    Local Opaque pgte_write_spec.

    Variable b_set_mapping: block.
    Hypothesis h_set_mapping_s : Genv.find_symbol ge _set_mapping = Some b_set_mapping.
    Hypothesis h_set_mapping_p : Genv.find_funct_ptr ge b_set_mapping
                                 = Some (External (EF_external _set_mapping
                                                  (signature_of_type (Tcons tulong (Tcons tulong Tnil)) tvoid cc_default))
                                        (Tcons tulong (Tcons tulong Tnil)) tvoid cc_default).
    Local Opaque set_mapping_spec.

    Variable b_granule_get: block.
    Hypothesis h_granule_get_s : Genv.find_symbol ge _granule_get = Some b_granule_get.
    Hypothesis h_granule_get_p : Genv.find_funct_ptr ge b_granule_get
                                 = Some (External (EF_external _granule_get
                                                  (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                        (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque granule_get_spec.

    Variable b_granule_unlock: block.
    Hypothesis h_granule_unlock_s : Genv.find_symbol ge _granule_unlock = Some b_granule_unlock.
    Hypothesis h_granule_unlock_p : Genv.find_funct_ptr ge b_granule_unlock
                                    = Some (External (EF_external _granule_unlock
                                                     (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                           (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque granule_unlock_spec.


    Lemma data_create_body_correct:
      forall m d d' env le g_rd_base g_rd_offset data_addr map_addr g_data_base g_data_offset g_src_base g_src_offset res
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTg_rd: PTree.get _g_rd le = Some (Vptr g_rd_base (Int.repr g_rd_offset)))
             (HPTdata_addr: PTree.get _data_addr le = Some (Vlong data_addr))
             (HPTmap_addr: PTree.get _map_addr le = Some (Vlong map_addr))
             (HPTg_data: PTree.get _g_data le = Some (Vptr g_data_base (Int.repr g_data_offset)))
             (HPTg_src: PTree.get _g_src le = Some (Vptr g_src_base (Int.repr g_src_offset)))
             (Hspec: data_create_spec0 (g_rd_base, g_rd_offset) (VZ64 (Int64.unsigned data_addr)) (VZ64 (Int64.unsigned map_addr)) (g_data_base, g_data_offset) (g_src_base, g_src_offset) d = Some (d', VZ64 (Int64.unsigned res))),
           exists le', (exec_stmt ge env le ((m, d): mem) data_create_body E0 le' (m, d') (Out_return (Some (Vlong res, tulong)))).
    Proof.
      solve_code_proof Hspec data_create_body.
      -  eexists. solve_proof_low.
         rewrite <- H1. simpl. somega.
      - eexists. solve_proof_low.
        rewrite <- H1. simpl. somega.
      - eexists. repeat big_vcgen.
        rewrite <- H1. simpl. somega.
        rewrite <- H1. simpl. somega. somega.
        solve_func64 z1. reflexivity. symmetry. solve_proof_low.
        solve_func z2.  reflexivity. symmetry. sstep. assumption. somega.
        rewrite <- H1. solve_proof_low. somega. somega. somega.
        simpl.
        repeat big_vcgen.
        solve_func64 z5. reflexivity. symmetry. solve_proof_low.
        solve_proof_low. somega. somega. somega. somega. somega.
        simpl. repeat big_vcgen.
        somega.
        assert(ns_buffer_read_data_spec 0 (p6, z6) r2 = Some (r3, Int.unsigned (Int.repr 0))).
        sstep. assumption. somega. eassumption.
        solve_proof_low.
        simpl.
        repeat big_vcgen.
        simpl. repeat vcgen.
        reflexivity.
        simpl. big_vcgen. repeat vcgen.
        discriminate.
        reflexivity.
        simpl. repeat vcgen.
        simpl. repeat vcgen.
        simpl. repeat vcgen.
      - eexists. repeat big_vcgen.
        somega.
        solve_func64 z1. reflexivity. symmetry. solve_proof_low.
        solve_func z2.  reflexivity. symmetry. sstep. assumption. somega.
        solve_proof_low.
        simpl. repeat big_vcgen.
        solve_func64 z5. reflexivity. symmetry. solve_proof_low.
        solve_proof_low. somega. somega. somega. somega. somega. somega. somega.
        somega.
        simpl. repeat big_vcgen.
        simpl. somega.
        assert(ns_buffer_read_data_spec (Int64.unsigned res) (p6, z6) r2 = Some (r3, Int.unsigned (Int.repr z7))).
        sstep. assumption. somega. eassumption. somega. somega.
        solve_proof_low. somega. somega. somega.
        simpl. repeat big_vcgen.
        unfold Int64.or. repeat sstep. simpl in C34. assumption.
        somega. apply or_le_64. omega. omega. somega. somega. somega. somega.
        simpl. repeat vcgen.
        somega. reflexivity.
        simpl. repeat vcgen. somega. reflexivity.
        simpl. repeat vcgen.
        simpl. repeat vcgen. somega. reflexivity.
        simpl. repeat vcgen. somega.
    Qed.

  End BodyProof.

End CodeProof.
