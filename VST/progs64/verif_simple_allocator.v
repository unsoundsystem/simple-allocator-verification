Require Import ZArith.
Require Import VST.floyd.proofauto.
Require Import VST.progs64.simple_allocator.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Section mpred.

Context `{!default_VSTGS Σ}.
Check f_slab_init.
Check Vundef.
Check reptype (Tstruct _slab noattr).
Compute Ews.
Definition tslab := Tstruct _slab noattr.
Compute reptype tslab.

Definition CHUNK_SIZE: Z := 1024.
Definition ENTRY_SIZE: Z:= 4.
Check memory_block.

Definition slab_init_spec :=
  DECLARE _slab_init
  WITH slab: val, gv: globals, chunk: val
  PRE [ (tptr tslab) ]
    PROP()
    PARAMS (slab) GLOBALS (gv)
    SEP (data_at Ews tslab (Vundef, (Vundef, Vundef)) slab)
  POST [ tvoid ]
    PROP() RETURN()
    SEP (data_at Ews tslab (Vptrofs (Ptrofs.repr CHUNK_SIZE), (Vptrofs (Ptrofs.repr ENTRY_SIZE), gv __space)) slab).

(*memory_block Ews CHUNK_SIZE p*)
Check semax_body.
Check⊤. 
Check memory_block_data_at__tarray_tuchar_eq.
Check tptr tuchar.
(*Definition slab_inv (slab: val) (p: val) (buf: val) :=*)
  (*field_at slab (DOT _chunk) *)
Print memory_block.
Print valid_pointer'.
Check memory_block_valid_pointer.
Check Vptr.

Print gfield.
Search "array".
Definition slab_alloc_spec :=
  DECLARE _slab_alloc
  WITH slab: val, chunksize: Z, entry_size: Z, chunk: val, chunk_block: block, 
  b: block, gv: globals
  PRE [ tptr tslab ]
    PROP(entry_size <= chunksize;
        0 <= chunksize <= Ptrofs.max_unsigned;
        0 <= entry_size <= Ptrofs.max_unsigned;
        slab <> nullval;
        chunk = Vptr chunk_block (Ptrofs.repr 0);
        chunk_block = b
    )
    PARAMS (slab)
    GLOBALS (gv)
    SEP (
        memory_block Ews CHUNK_SIZE (Vptr b (Ptrofs.repr 0));
        data_at Ews tslab (Vptrofs (Ptrofs.repr chunksize),
          (Vptrofs (Ptrofs.repr entry_size),
            chunk)) slab
    )
  POST [ tptr tvoid ] ∃res:val, 
    PROP()
    (*LOCAL(lvar _r chunk)*)
    RETURN(chunk)
    SEP (valid_pointer chunk;
        data_at Ews tslab (Vptrofs (Ptrofs.repr (chunksize - entry_size)),
        (Vptrofs (Ptrofs.repr entry_size),
            offset_val entry_size chunk)) slab
    ).

Definition Gprog : funspecs := ltac:(with_library prog [slab_alloc_spec; slab_init_spec]).

Lemma body_slab_init: semax_body Vprog Gprog f_slab_init slab_init_spec.
Proof.
  start_function.
  repeat forward.
  entailer!.
Qed.


Check Vprog.
(* seems important ingrediant *)
Check memory_block_valid_pointer.
Print memory_block.
Check memory_block_data_at__tarray_tuchar_eq.
(*Check fun (gv: globals) => memory_block_data_at__tarray_tuchar_eq Ews (gv __space) CHUNK_SIZE.*)
(*Check fun (gv: globals) => memory_block_valid_pointer Ews CHUNK_SIZE (gv __space).*)
(*Search memory_block .*)
(*Check Ptrofs.unsigned_repr.*)

    (*field_at Ews tslab (DOT Check_entry_size) (Vlong (Int64.repr entry_size)) slab;*)
    (*field_at Ews tslab (DOT _chunksize) (Vlong (Int64.repr chunksize)) slab*)

(*Search "addrof".*)
Print  offset_val.

(* valid_pointer chunk must be provable from this *)
(*Definition slab_invariant (slab: val) chunksize entry_size chunk chunk_block chunk_ofs (gv: globals)  :=*)
  (*data_at Ews tslab (Vptrofs (Ptrofs.repr chunksize), (Vptrofs (Ptrofs.repr entry_size), chunk)) slab*)
 (*∗  data_at Ews (tptr tuchar) (Vptr chunk_block chunk_ofs) chunk.*)
(*Check slab_invariant.*)
(*Search is_pointer_or_null.*)

Lemma body_slab_alloc: semax_body Vprog Gprog f_slab_alloc slab_alloc_spec.
Proof.
  start_function.
  repeat forward.
  forward_if.
  (*Search Int.unsigned (Int.repr _).*)
  (*Check Z.nle_gt.*)
  - forward. lia.
  - repeat forward.
    Check memory_block_valid_pointer.
    + rewrite (memory_block_valid_pointer Ews CHUNK_SIZE (Vptr b (Ptrofs.repr 0)) 0).
      rewrite offset_val_zero_Vptr. entailer. 
      * split;auto. lia.
      * auto.
Qed.

End mpred.
