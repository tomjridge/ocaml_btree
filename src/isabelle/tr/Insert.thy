theory Insert
imports Common
begin

section types

(* the stack records a list of pages, and the index within the page that was followed;
the page is always a nf
 *)
datatype ('r) stk = Stk "('r page_ref * nat) list"

definition dest_stk :: "'r stk => ('r page_ref * nat) list" where
  "dest_stk stk == (case stk of Stk xs => xs)"

definition stk_cons :: "'r stk => ('r page_ref * nat) => 'r stk" where
  "stk_cons stk rn == (case stk of 
    Stk xs => Stk(rn # xs))"

definition stk_size :: "'r stk => nat" where
  "stk_size stk == (case stk of (Stk xs) => size(xs))"


section "tree substitution"

(* we need to construct the tree, given a stack and a subtree (or two subtrees) *)

function tree_subst :: "('bs,'k,'r,'v) ctxt_p2f_t => ('bs,'r) store => 
  ('k,'v) tree => (* given a subtree *)
  'r stk => (* and a stack identifying the subtree *)
  ('k,'v) tree option" (* return the new tree resulting from substituting the given subtree *)
where
  "tree_subst c0 s0 t0 stk0 = (
    case stk0 of 
    Stk [] => (Some t0)
    | Stk ((r0,n0)#stk1) => (
      let h0 = arb in (* FIXME what to do about height?! *)
      let t1 = page_ref_to_tree c0 s0 r0 h0 in
      let t2 = (
        case t1 of
        None => (Error |> rresult_to_option)
        | Some x =>(
          case x of
          Tr_lf _ => (Error |> rresult_to_option) (* impossible if stk wf *)
          | Tr_nd(n,ks,ts) => (
            let t0' = Tr_nd(n,ks,ts(n0 := t0)) in
            tree_subst c0 s0 t0' (Stk(stk1))
          ))
        )
      in
      t2)
)"
by pat_completeness auto
termination
  apply(force intro:FIXME)
  done

(* in one step, the effect of substitution at position n is... *)

definition tree_subst_1 :: "('bs,'k,'r,'v) ctxt_p2f_t => ('bs,'r) store => 
  ('k,'v) tree => (* given a subtree *)
  ('r page_ref * nat) => (* and a stack frame identifying the subtree *)
  ('k,'v) tree option" (* return the new tree resulting from substituting the given subtree *)
where
  "tree_subst_1 c0 s0 t0 r0n0 == (
      let (r0,n0) = r0n0 in
      let h0 = arb in (* FIXME what to do about height?! *)
      let t1 = page_ref_to_tree c0 s0 r0 h0 in
      let t2 = (
        case t1 of
        None => (Error |> rresult_to_option)
        | Some x =>(
          case x of
          Tr_lf _ => (Error |> rresult_to_option) (* impossible if stk wf *)
          | Tr_nd(n,ks,ts) => (
            let t0' = Tr_nd(n,ks,ts(n0 := t0)) in
            Some(t0')
          ))
        )
      in
      t2)
"

(* for tree contexts, it is convenient to work with partial trees, where a node may map to none;
instead, we use the degenerate node Tr_nd[]
 *)


(* tree_subst_1 has the following property; 
FIXME need to distinguish the types of failure and success; roughly there is a failure
"at this level", and a failure at a lower level (which we don't care too much about the nature of)

we really need to move to a formalization with a "hole"; does thiemann et al have a notion of 
leaves and the effect of hole substitution?

need to get some version of his stuff


*)
lemma exists_kvs_l_kvs_r: "? kvs_l kvs_r.
(((tree_subst_1 c0 s0 (Tr_nd(0,ks,ts)) (r0,n0)) |> (Option.map_option tree_to_leaves)) 
  = Some(kvs_l@[]@kvs_r))
& (length kvs_l = n0)
"
  sorry

lemma "
(((tree_subst_1 c0 s0 (Tr_nd(0,ks,ts)) (r0,n0)) |> tree_to_leaves) = kvs_l@[]@kvs_r)
& (length kvs_l = n0)
"
oops




(* want to know what the effect of substituting a tree is, in terms of the leaves; we need to know
the following holds for our defn of tree subst; the problem is how to get kvs_l and kvs_r *)

lemma "
! stk0. (stk_size(stk0) = n0)
--> (? kvs_l kvs_r. ! t0 kvs_c. 
  ((t0 |> tree_to_leaves) = ((kvs_c)))
  --> ((tree_subst c0 s0 t0 stk0) |> (map_option tree_to_leaves) = Some(kvs_l@kvs_c@kvs_r)))
"
apply(induct_tac n0)
 apply(intro allI impI)
 apply(rule_tac x="[]" in exI)
 apply(rule_tac x="[]" in exI)
 apply(intro allI impI)
 apply(subgoal_tac "stk0 = Stk[]") prefer 2 apply (metis case_stk_def length_0_conv stk.exhaust stk.rec stk_size_def)
 apply(simp)
 apply (metis option.simps(9) rev_apply_def)

 (* size stk0 = Suc n *)
 apply(intro allI impI)
 apply(case_tac stk0)
 apply(case_tac list) apply (metis list.size(3) old.nat.distinct(2) stk.case stk_size_def)
 apply(rename_tac rn stk1)
 apply(erule_tac x="Stk(stk1)" in allE)
 apply(erule_tac impE) apply(force simp add: stk_size_def)
 apply(simp)
 apply(elim exE)
 



lemma tree_subst_tree_to_leaves: "
  (! t0 kvs_c. 
    ((t0 |> tree_to_leaves) = ((kvs_c)))
    -->(tree_subst c0 s0 t0 stk0) |> (map_option tree_to_leaves) = Some(kvs_l@kvs_c@kvs_r))
  --> True
"
oops

section "parameters"

section "insert,  ins_state, ins_step"

record ('bs,'k,'r,'v) ins_state_down = 
  isd_k :: "'k key"
  isd_v :: "'v value_t"
  isd_r :: "'r page_ref"
  isd_stk :: "'r stk"
  isd_str :: "('bs,'r) store"

record ('r) ins_state_up_1 = 
  (* r is the node we have just come from ie the node we just modified *)
  isu1_r :: "'r page_ref"
  
(* r1 <= k < r2 *)
record ('k,'r,'v) ins_state_up_2 = 
  isu2_r1 :: "'r page_ref"
  isu2_k :: "'k key"
  isu2_r2 :: "'r page_ref"

datatype ('k,'r,'v) ins_state_up' = 
  S "'r ins_state_up_1"  (* inserting a single pointer *)
  | D "('k,'r,'v) ins_state_up_2"  (* inserting two pointers, separated by a key *)

record ('bs,'k,'r,'v) ins_state_up =
  isu_s :: "('k,'r,'v) ins_state_up'"
  isu_stk :: "'r stk"
  isu_str :: "('bs,'r) store"

datatype ('bs,'k,'r,'v) ins_state = 
  Down "('bs,'k,'r,'v) ins_state_down"
  | Up "('bs,'k,'r,'v) ins_state_up"
  | Ret "('r page_ref * ('bs,'r) store)"


definition ins_step :: "('bs,'k,'r,'v) ctxt_k2r_t
  => ('bs,'k,'r,'v) ins_state 
  =>  ('bs,'k,'r,'v) ins_state option" where
  "ins_step ctxt1 is0 == (
case is0 of
    Down isd => (
      let r0 = isd|>isd_r in
      let frm = (page_ref_to_frame (ctxt_p2f_t.truncate ctxt1) (isd|>isd_str) r0) in
      case frm of
      None => None
      | Some frm0 => (
        case frm0 of
        Frm_I nf => (  
          let k2r = ((ctxt1|>key_to_ref2)|>dest_key_to_ref) in
          let k0 = (isd|>isd_k) in
          let i = k2r nf k0 in (* we need the index *)
          let r' = (nf|>nf_rs) i in
          let stk = (isd|>isd_stk) in
          let stk' = stk_cons stk (r0,i) in
          Some(Down(isd \<lparr> isd_r:= r', isd_stk:=stk'  \<rparr>))
        )
        | Frm_L lf => (
          (* we do the insert, no split case *)
          let kvs = (lf |> lf_kvs) in
          let (k,v) = (isd |> isd_k, isd |> isd_v) in
          let kvs' = (k,v)#kvs in
          let (s0::('bs,'r)store,r') = arb (* new_ref (s0|>isd_str) *) in
          let s0 = arb (* write_frame s0 r (Frm_L \<lparr> lf_kvs:=kvs' \<rparr>) *) in
          let isu1 = \<lparr> isu1_r=r' \<rparr> in
          let isu' = S(isu1) in
          let isu = \<lparr> isu_s = isu', isu_stk = (isd |> isd_stk), isu_str = s0 \<rparr> in
          Some(Up isu)
        )
      )
    )
    | Up isu => (
      let (isu',stk,s0) = (isu|>isu_s,isu|>isu_stk,isu|>isu_str) in
      case isu' of
      S isu1 => (
        let r = isu1|>isu1_r in
        case stk of Stk([]) => Some(Ret(r,s0)) 
        | Stk((r2,n2)#rns) => (
          (* we need to insert r in the place recorded in the stack *)
          let frm = (page_ref_to_frame (ctxt_p2f_t.truncate ctxt1) s0 r2) in
          case frm of None => (Error |> rresult_to_option) | Some x => (case x of
          Frm_I nf => (
            let (s0::('bs,'r)store,r'::'r page_ref) = arb (* new ref *) in
            let nf'::('r,'k) node_frame = arb nf r n2 in (* substitute *)
            let s0::('bs,'r)store = arb s0 r' nf' in (* write new page *) 
            let isu1 = \<lparr> isu1_r=r' \<rparr> in
            let isu' = S(isu1) in
            let isu = \<lparr> isu_s = isu', isu_stk = (Stk(rns)), isu_str = s0 \<rparr> in
            Some(Up isu) )
          | _ => impossible (* ins_step: impossible *)
          )))
      | D isu2 => arb
      
    )
    
  )"



end


