theory Common 
imports Main
begin


section "preliminaries"

definition rev_apply :: "'a => ('a => 'b) => 'b" (infixl "|>" 100) where
  "rev_apply x f = f x"


(* Quickcheck_Examples/Completeness.thy - should be in Main? simpler defn here*)
definition is_Some :: "'a option => bool" where
  "is_Some x == x ~= None"

primrec dest_Some (* :: "'a option => 'a" *) where 
  "dest_Some (Some x) = x"
  | "dest_Some None = undefined"


definition arb :: "'a" where
  "arb == undefined"  

definition impossible :: "'a" where
  "impossible == undefined"  

datatype 'a rresult = Ok 'a | Error 

definition rresult_to_option :: "'a rresult => 'a option" where
  "rresult_to_option x = (case x of Ok x => Some x | Error => None)"

lemma [simp]: "(Error |> rresult_to_option = None) & ((Ok x) |> rresult_to_option = Some x)"
  apply(force simp: rresult_to_option_def rev_apply_def)
  done



section "page, page_ref, store"

(* type vars: 'bs 'k 'r 'v *)

datatype 'bs page = Page 'bs (* bytes *)

datatype 'r page_ref = Page_ref 'r

definition dest_page_ref :: "'r page_ref => 'r" where
  "dest_page_ref r0 == (case r0 of Page_ref r => r)"

datatype ('r,'bs) store = Store "('r page_ref ~=> 'bs page)"  (* different to paper: we store actual bytes *)

definition dest_store :: "('r,'bs) store => ('r page_ref ~=> 'bs page)" where
  "dest_store s0 == (case s0 of Store f => f)"

definition ref_to_page :: "('r,'bs) store => 'r page_ref => 'bs page option" where
  "ref_to_page s0 r0 == (s0|>dest_store) r0"


section "key and frame, (leaf_frame) key_to_v"


datatype 'k key = Key 'k

definition dest_key :: "'k key => 'k" where
  "dest_key k = (case k of Key k => k)"


datatype 'v value_t = Value 'v

definition dest_value :: "'v value_t => 'v" where
  "dest_value v == (case v of Value v => v)"


record ('r,'k) node_frame = 
  nf_n :: "nat"
  nf_ks :: "nat => 'k key"
  nf_rs :: "nat => 'r page_ref"

record ('k,'v) leaf_frame = 
  lf_kvs :: "('k key * 'v value_t) list" (* slightly different to paper - we store ks in tree *) 

datatype ('r,'k,'v) frame = Frm_I "('r,'k) node_frame" | Frm_L "('k,'v) leaf_frame"

definition key_to_v :: "('k,'v) leaf_frame => 'k key => 'v value_t option" where
  "key_to_v lf k == (lf |> lf_kvs |> map_of) k"



section "page and frame, page_to_frame, ctxt_p2f"

(* interpretation of pages *)
datatype ('bs,'k,'r,'v) page_to_frame = P2f "'bs page => ('r,'k,'v) frame"  (* note that this forces that the page internally stores its type; this is not necessary, but is used by step_find *)

definition dest_p2f :: "('bs,'k,'r,'v) page_to_frame => 'bs page => ('r,'k,'v) frame" where
  "dest_p2f x = (case x of P2f f => f)"

(**********)
(* to convert a page_ref to a frame, lookup the page option and use the above *)
record  ('bs,'k,'r,'v) ctxt_p2f_t =
  ctxt_p2f :: "('bs,'k,'r,'v) page_to_frame"

(* from this point, we don't duplicate 0/Suc defns, to minimize # of defns *)
definition page_ref_to_frame :: "('bs,'k,'r,'v) ctxt_p2f_t => ('r,'bs) store =>  'r page_ref => ('r,'k,'v) frame option" where
  "page_ref_to_frame c0 s0 r0 == (
    case ref_to_page s0 r0 of
    None => (Error |> rresult_to_option)  (* invalid page access *)
    | Some p => (Some( (c0|>ctxt_p2f|>dest_p2f) p))
)"



section "tree"

datatype ('k,'v) tree = Tr_nd "(nat * (nat => 'k key) * (nat => ('k,'v) tree))" | Tr_lf "('k key * 'v value_t) list"

type_synonym tree_height = nat

lemma FIXME: "P" sorry

function tree_to_kvs :: "('k,'v) tree => ('k key *'v value_t) list" where
  "tree_to_kvs (Tr_lf(kvs)) = kvs"
  | "tree_to_kvs (Tr_nd(n,ks,ts)) = ([0..<n+1] |> (List.map ts) |> (List.map tree_to_kvs) |> List.concat)" (* we use n+1 because there must be n (i.e. number of keys + 1 departing from index 0) subtrees in each internal node*)
by pat_completeness auto
termination  (* tree_to_kvs_dom is not right here - the function package seems confused FIXME *)
  apply(force intro:FIXME)
  done


section "page_ref_to_tree, page_ref_to_map, page_ref_key_to_v"

(* NB this has an explicit n argument, whereas wfness gives us that we can just use page_ref_to_frame *)
fun page_ref_to_tree :: "('bs,'k,'r,'v) ctxt_p2f_t =>  ('r,'bs) store => 'r page_ref => tree_height => ('k,'v) tree option" where
  "page_ref_to_tree c0 s0 r0 0 = (
      case page_ref_to_frame c0 s0 r0 of 
      None => (Error |> rresult_to_option) 
      | Some frm => (
        case frm of 
        Frm_L(lf) => (Some(Tr_lf (lf|>lf_kvs)))
        | _ => (Error |> rresult_to_option )))"  (* attempt to access missing page *)
  | "page_ref_to_tree c0 s0 r0 (Suc n') = (
      case page_ref_to_frame c0 s0 r0 of
      None => (Error |> rresult_to_option)  (* attempt to access missing page *)
      | Some frm => (
        case frm of 
        Frm_I(nf) => (
          let n = (nf|>nf_n) in
          let ks = (nf|>nf_ks) in
          let rs = (nf|>nf_rs) :: (nat => 'r page_ref) in
          let f0 = (% r. page_ref_to_tree c0 s0 r n') :: ('r page_ref => ('k,'v) tree option) in
          let prop = (! (m::nat). m <= n --> m |> rs |> f0 |> is_Some) in (* we use \<le> because the number of subtrees to create is n (number of keys) + 1 --since we start from index 0, it is just n*)
          case prop of
          True => (Some(Tr_nd(n,ks,(% (m::nat). m |> rs |> f0 |> dest_Some))))
          | False => (Error |> rresult_to_option))  (* Frm_I was not wellformed - prop was false *)
        | Frm_L(_) => (Error |> rresult_to_option)))"  (* found Frm_L but tree_height was not 0 *)

(* notice that this ideally belongs in section "page and frame" *)
definition page_ref_to_kvs ::  "('bs,'k,'r,'v) ctxt_p2f_t =>  ('r,'bs) store => 'r page_ref => tree_height => ('k key*'v value_t) list option" where
  "page_ref_to_kvs c0 s0 r0 n0 == (
  (page_ref_to_tree c0 s0 r0 n0)
  |> (% x. case x of
    None => None
    | Some t => Some(tree_to_kvs t)))"

definition kvs_to_map :: "('k key*'v value_t) list => ('k key ~=> 'v value_t)" where
  "kvs_to_map kvs == (map_of kvs)"

definition page_ref_to_map :: "('bs,'k,'r,'v) ctxt_p2f_t =>  ('r,'bs) store => 'r page_ref => tree_height => ('k key ~=> 'v value_t) option" where
  "page_ref_to_map c0 s0 r0 n0 == (page_ref_to_kvs c0 s0 r0 n0) |> (map_option kvs_to_map)"

definition page_ref_key_to_v :: "('bs,'k,'r,'v) ctxt_p2f_t => ('r,'bs) store => 'r page_ref => tree_height =>'k key => 'v value_t option" where
  "page_ref_key_to_v ctxt s0 r0 n0 k0 == (
    let m0 = page_ref_to_map ctxt s0 r0 n0 in
    Option.bind m0 (% m. m k0))"


section "(given node_frame) key_to_ref, ctxt_k2r_t"




(* NB we need some properties of these functions for correctness 

This abstracts from the particular find implementation. Essentially, at a non-leaf node, we need to map
a key to a page ref, from which we can continue the find. The property this function should have is
that, given a key, if there is a value corresponding to the key (which is unique), then the 
returned page ref identifies the relevant subtree.

*)
datatype ('bs,'k,'r,'v) key_to_ref = Key_to_ref "('r,'k) node_frame => 'k key => nat (* 'r page_ref *)" 
(* datatype ('bs,'k,'r,'v) key_to_v = Key_to_v "('k,'v) leaf_frame => 'k key => 'v option"  (* may be no such v *) - there is only one impl! *)

definition dest_key_to_ref :: "('bs,'k,'r,'v) key_to_ref => ('r,'k) node_frame => 'k key => nat (* 'r page_ref *)" where
  "dest_key_to_ref k2r == (case k2r of Key_to_ref f => f)"

(*
definition dest_key_to_v :: "('bs,'k,'r,'v) key_to_v => ('k,'v) leaf_frame => 'k key => 'v value_t option" where
  "dest_key_to_v k2v == (case k2v of Key_to_v f => f)"
*)

(**********)
record  ('bs,'k,'r,'v) ctxt_k2r_t =  "('bs,'k,'r,'v) ctxt_p2f_t" +
  key_to_ref2 :: "('bs,'k,'r,'v) key_to_ref"
(*  key_to_v :: "('bs,'k,'r,'v) key_to_v" *)

definition apply_key_to_ref :: "('bs,'k,'r,'v) key_to_ref => ('r,'k) node_frame  => 'k key => 'r page_ref" where
  "apply_key_to_ref k2r nf k0 == (
    let n = (dest_key_to_ref k2r) nf k0 in
    (nf|>nf_rs) n)"

end

