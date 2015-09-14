theory "Abstract_tree" 

imports 
 	 Main
begin

definition arb :: "'a" where
  "arb == SOME x. True"  (* where is this in lib? *)


(* type vars: 'bs 'k 'r 'v *)

datatype 'bs page = Page 'bs (* bytes *)

datatype 'r page_ref = Page_ref 'r

datatype ('r,'bs) store = Store "('r ~=> 'bs page)"  (* different to paper: we store actual bytes *)


datatype 'k key = Key 'k

record ('r,'k) node_frame = 
  nf_n :: "nat"
  nf_ks :: "nat => 'k key"
  nf_ps :: "nat => 'r page_ref"

record ('k,'v) leaf_frame = 
  lf_kvs :: "('k * 'v) list" (* slightly different to paper - we store ks in tree *) 

datatype ('r,'k,'v) frame = Frm_I "('r,'k) node_frame" | Frm_L "('k,'v) leaf_frame"

(* interpretation of pages *)
datatype ('bs,'k,'r,'v) page_to_frame_0 = P2f0 "'bs page => ('k,'v) leaf_frame"
datatype ('bs,'k,'r,'v) page_to_frame_suc = P2fs "'bs page => ('r,'k) node_frame"

(* to convert a page_ref to a frame, lookup the page option and use the above *)


datatype ('k,'v) tree = Tr_nd "(nat * (nat => 'k key) * (nat => ('k,'v) tree))" | Tr_lf "('k * 'v) list"

definition page_ref_to_tree :: "('r,'bs) store => 'r page_ref => nat => ('k,'v) tree option" where
  "page_ref_to_tree s0 r0 n0 == arb::('k,'v)tree option"

(*
locale l0 = 
  fixes r0:: "'r store_ref" 
  and s0:: "('a,'b,'r) store"
*)

end