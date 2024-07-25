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
Definition tfreelist := Tstruct _freelist noattr.
Compute reptype tslab.
Definition slab_init_spec :=
  DECLARE _slab_init
  WITH slab: val, p: val, chunksize: val, entry_size: val
  PRE [ (tptr tslab), tptr tuchar, tulong, tulong ]
    PROP()
    PARAMS (slab; p; chunksize; entry_size)
    SEP (data_at Ews tslab (Vundef, (Vundef, (Vundef, Vundef))) slab)
  POST [ tvoid ]
    PROP() RETURN()
    SEP (data_at Ews tslab (chunksize, (entry_size, (p, Vnullptr))) slab).

Definition Gprog : funspecs := ltac:(with_library prog [slab_init_spec]).

Check semax_body.
Check⊤. 
Lemma body_slab_init: semax_body Vprog Gprog f_slab_init slab_init_spec.
Proof.
  start_function.
  repeat forward.
  entailer!.
Qed.
End mpred.
