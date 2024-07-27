Require Import ZArith.
Require Import VST.floyd.proofauto.
Require Import VST.progs64.simple_allocator.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Section mpred.

Context `{!default_VSTGS Σ}.

Definition tslab := Tstruct _slab noattr.

Definition CHUNK_SIZE: Z := 1024.
Definition ENTRY_SIZE: Z:= 4.

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


(*
   NOTE: 事前条件が一部のパスしかカバーしていない
   また､_spaceの存在とは別に事前条件にプールがあることを言明している

   TODO: tarrayをmemory_blockとして扱うやり方が分からなかった｡
   当初は_spaceの存在からmemory_blockを導出してmemory_block_valid_pointerを使って結論するつもりだった
 *)
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

Lemma body_slab_alloc: semax_body Vprog Gprog f_slab_alloc slab_alloc_spec.
Proof.
  start_function.
  repeat forward.
  forward_if.
  - forward. lia.
  - repeat forward.
    Check memory_block_valid_pointer.
    + rewrite (memory_block_valid_pointer Ews CHUNK_SIZE (Vptr b (Ptrofs.repr 0)) 0).
      rewrite offset_val_zero_Vptr. entailer. 
      * split;auto. lia.
      * auto.
Qed.

End mpred.
