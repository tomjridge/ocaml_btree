theory "Find" 

imports 
 	 Common "~~/src/HOL/Library/Multiset" (* for size_change *)
begin




section "find, find_state, fs_step"

(* find *)
record ('bs,'k,'r,'v) find_state_l =
  fsl_k :: "'k key"
  fsl_r :: "'r page_ref"
(*   fnd0_s :: "('bs,'r) store" *)

record ('bs,'k,'r,'v) find_state_r =
  fsr_r :: "'r page_ref"
  fsr_v :: "'v value_t option"
(*  fnd1_s :: "('bs,'r) store" *)

datatype ('bs,'k,'r,'v) find_state = Fs_l "('bs,'k,'r,'v) find_state_l" | Fs_r "('bs,'k,'r,'v) find_state_r"

definition find_state_to_page_ref :: "('bs,'k,'r,'v) find_state => 'r page_ref" where
  "find_state_to_page_ref fs0 = (case fs0 of
    Fs_l fsl => (fsl|>fsl_r)
    | Fs_r fsr => (fsr |> fsr_r))"

definition fs_step :: "('bs,'k,'r,'v) ctxt_k2r_t
  => (('bs,'r) store * ('bs,'k,'r,'v) find_state) 
  => (('bs,'k,'r,'v) find_state) option" where
  "fs_step ctxt1 s0fs0 == (
  let (s0,fs0) = s0fs0 in
  case fs0 of
  Fs_l fsl => (
    let r0 = (fsl|>fsl_r) in
    let k0 = (fsl|>fsl_k) in
    case (page_ref_to_frame (ctxt_p2f_t.truncate ctxt1) s0 r0) of 
    None => (Error |> rresult_to_option)  (* invalid page access *)
    | Some frm => (
      case frm of 
      Frm_I nf => (
        let r' = apply_key_to_ref (ctxt1|>key_to_ref2) nf k0 in
        Some(Fs_l (fsl (| fsl_r := r' |))))
      | Frm_L lf => (
        let k2v = key_to_v in
        let v = k2v lf k0 in
        Some(Fs_r (| fsr_r = r0, fsr_v = v |)))))
  | Fs_r fsr => (Error |> rresult_to_option))"  (* attempt to step Fs_r *)


section "fs_step as a function"

text "iterate the fs_step function n times"

(* FIXME in the following we may want to use a standard isabelle while construction *)
definition fs_step_as_fun :: "('bs,'k,'r,'v) ctxt_k2r_t 
  => tree_height
  => (('bs,'r) store * ('bs,'k,'r,'v) find_state) 
  => (('bs,'k,'r,'v) find_state)" where
  "fs_step_as_fun ctxt1 n0 s0fs0 == (
  let (s0,fs0) = s0fs0 in
  let f0 = % x. (s0,x) |> (fs_step ctxt1) |> dest_Some in
  (Nat.funpow n0 f0) fs0)"


section "wellformedness predicates"

(* FIXME obviously the following need to be filled in properly *)

definition wf_ctxt:: "('bs,'k,'r,'v) ctxt_k2r_t => bool" where
  "wf_ctxt ctxt == True"

definition wf_ctxt1:: "('bs,'k,'r,'v) ctxt_k2r_t => bool" where
  "wf_ctxt1 ctxt1 == 
  ! s0 r0 ctxt nf k0 r' v0 n0 m1 m1'.
(ctxt_p2f_t.truncate ctxt1 = ctxt)
(* if r0 is not a leaf *)
& (page_ref_to_frame ctxt s0 r0 = Some (Frm_I nf))
(* and the map exists at r0 *)
& (page_ref_to_map ctxt s0 r0 n0 = Some m1)
(* and we descend to r' *)
& (apply_key_to_ref (ctxt1|>key_to_ref2) nf k0 = r')
(* and the map exists at r' *)
& (page_ref_to_map ctxt s0 r' (n0 - Suc 0) = Some m1')
(* then the maps agree, at least for the key *)
& (m1 k0 = v0)
--> (m1' k0 = v0)
"


(*
definition wf_store_page_ref_to_map_none :: "('bs,'k,'r,'v) ctxt_k2r_t => ('bs,'r) store => tree_height => 'r page_ref => bool" where
  "wf_store_page_ref_to_map_none  c1 s0 n0 r0 == (
    let c0 = ctxt_p2f_t.truncate c1 in
    ((page_ref_to_map c0 s0 r0 n0 = None) --> False)
  )"
*)

definition wf_store_page_ref_to_map :: "('bs,'k,'r,'v) ctxt_k2r_t => ('bs,'r) store => tree_height => 'r page_ref => bool" where
  "wf_store_page_ref_to_map  c1 s0 n0 r0 == (
    let c0 = ctxt_p2f_t.truncate c1 in
(! m1 r' nf k0 . ((
(* if we have a map at r0 *)
(page_ref_to_map c0 s0 r0 n0 = Some m1)
& (page_ref_to_frame c0 s0 r0 = Some (Frm_I nf))
(* and we follow the key to r' *)
& (apply_key_to_ref (c1|>key_to_ref2) nf k0 = r')
(* then we still have a map *)
& (page_ref_to_map c0 s0 r' (n0 - Suc 0) = None)
) --> False
))  (* FIXME does this follow from page_ref_to_map ~= None? FIXME isn't this a basic property of the defn of page_ref_to_map/page_ref_to_tree? *)
& (page_ref_to_map c0 s0 r0 n0 ~= None)    
  )"


definition wf_store:: "('bs,'k,'r,'v) ctxt_k2r_t => ('bs,'r) store => tree_height => 'r page_ref => bool" where
  "wf_store c1 s0 n0 r0 == (
(*    wf_store_page_ref_to_map_none c1 s0 n0 r0 *)
    wf_store_page_ref_to_map c1 s0 n0 r0

& True)"

(*

  

*)

section "correctness of fs_step"

definition fs_step_invariant :: "('bs,'k,'r,'v) ctxt_p2f_t
  => (('bs,'r) store * ('bs,'k,'r,'v) find_state)
  => tree_height
  => 'v value_t option
  => bool" where
  "fs_step_invariant ctxt s0fs0 n0 v0 == (
    let (s0,fs0) = s0fs0 in
    case fs0 of
    Fs_l fsl => (
      let k0 = (fsl|>fsl_k) in
      let r0 = (fsl|>fsl_r) in
      let v' = page_ref_key_to_v ctxt s0 r0 n0 k0 in
      v' = v0)
    | Fs_r fsr => (
      let v' = (fsr|>fsr_v) in
      v' = v0))"

(* FIXME in the following we want to eliminate n0 and v0 explicit arguments, and phrase as a
simple invariant; v0 can be a parameter of the invariant; how do we get n0? just say I v0 == ! n0. wf_store s0 n0... --> *)
lemma fs_step_is_invariant: "
  ! (ctxt1::('bs,'k,'r,'v) ctxt_k2r_t) ctxt s0 fs0 n0 v0.
  ((ctxt_p2f_t.truncate ctxt1) = ctxt)
  --> wf_ctxt1 ctxt1 & wf_store ctxt1 s0 n0 (fs0|>find_state_to_page_ref)
  --> (
  fs_step_invariant ctxt (s0,fs0) n0 v0 --> (
  let x = fs_step ctxt1 (s0,fs0) in
  case x of 
  None => True  (* if we are at a Fs_r, no further facts are available *)
  | Some (fs') => (
    (* n0 could be 0? but then fs' is Fs_r? *)
    fs_step_invariant ctxt (s0,fs') (n0 - 1) v0)))"
  apply(rule)+
  apply(elim conjE)
  apply(subgoal_tac "? x. fs_step ctxt1 (s0, fs0) = x")
   prefer 2
   apply(force)
  apply(erule exE)
  apply(simp add: Let_def)
  apply(case_tac x)
   (* none *)
   apply(force)

   (* x = Some a *)
   apply(simp)
   apply(rename_tac "fs'")
   apply(simp add: fs_step_def)
   apply(case_tac fs0)
    prefer 2
    apply(force)
   (* fs0 = Fs_l find_state_l_ex *)
   apply(simp)
   apply(rename_tac "fsl")
   apply(subgoal_tac "? r0. (fsl|>fsl_r) = r0")
    prefer 2 apply(force)
   apply(subgoal_tac "? k0. (fsl|>fsl_k) = k0 ")
    prefer 2 apply(force)
   apply(erule exE)+
   apply(case_tac " (page_ref_to_frame (ctxt_p2f_t.truncate ctxt1) s0 r0)")
    apply(force)

    (*  (page_ref_to_frame (ctxt_p2f_t.truncate ctxt1) s0 r0) = Some r' *)
    apply(rename_tac frm')
    apply(simp)
    apply(case_tac frm')
     (**********)
     (* frm' = Frm_I node_frame_ext *)
     apply(rename_tac nf)  (* nf = node_frame *)
     apply(simp)
     apply(thin_tac "fs0 = ?x")
     apply(thin_tac "frm' = ?x")
     apply(thin_tac "x=?x")
     apply(subgoal_tac "? r'. apply_key_to_ref (ctxt1 |> key_to_ref2) nf k0 = r'") prefer 2 apply(force)
     apply(erule exE)
     apply(subgoal_tac "? fsl'. (fsl\<lparr>fsl_r := r'\<rparr>) = fsl'")      prefer 2 apply(force)
     apply(erule exE)
     apply(simp)
     (* note how this goal is concise and readable *)
     apply(simp add: fs_step_invariant_def)
     apply(drule_tac t="fs'" in sym)
     apply(simp)
     apply(thin_tac "fs' = ?x")
     apply(drule_tac t="fsl'" in sym)
     apply(simp)
     apply(subgoal_tac "fsl\<lparr>fsl_r := r'\<rparr> = (| fsl_k = k0, fsl_r = r' |)") prefer 2  apply(metis (full_types) find_state_l.surjective find_state_l.update_convs(2) old.unit.exhaust rev_apply_def) 
     apply(thin_tac "fsl' = fsl\<lparr>fsl_r := r'\<rparr> ")
     apply(simp)
     apply(simp add: rev_apply_def)
     apply(simp add: page_ref_key_to_v_def)
     (* page_ref_to_map could be none or some *)
     apply(subgoal_tac "? m0. (page_ref_to_map (ctxt_p2f_t.truncate ctxt1) s0 r0 n0) = m0")
      prefer 2 apply(force)
     apply(erule exE)
     apply(simp)
     apply(case_tac m0)
      (* m0 = None *)
      apply(simp)
      (* this case ruled out by wellformedness - page_ref_to_map cannot be None *)
      apply (metis find_state.simps(5) find_state_to_page_ref_def rev_apply_def wf_store_def wf_store_page_ref_to_map_def)
      
      (* m0 = Some a *)
      apply(rename_tac m1)
      apply(simp)
      apply(thin_tac "m0 = ?x")
      apply(subgoal_tac "? m0'.  (page_ref_to_map (ctxt_p2f_t.truncate ctxt1) s0 r' (n0 - Suc 0)) = m0'")
       prefer 2 apply(force)
      apply(erule exE)
      apply(simp)
      apply(case_tac "m0'")
       (* none - ruled out because m0 is_Some --> m0' is_Some ; FIXME sledgehammer should get this *)
       apply(simp)
       apply(simp add: wf_store_def wf_store_page_ref_to_map_def Let_def)
       apply(elim conjE)
       apply(erule exE)
       apply(simp add: page_ref_to_map_def page_ref_to_kvs_def rev_apply_def find_state_to_page_ref_def apply_key_to_ref_def)
       apply(elim exE conjE)
       apply(simp)
       apply (metis option.distinct(1))  

       (* m0' = Some a *)
       apply(rename_tac "m1'")
       apply(simp)
       apply(thin_tac "m0'=?x")
       (* m1 k0 = v0 --> m1' k0 = v0 ; this holds by wellformedness of key_to_ref, and page_ref_to_map Suc *)
       apply(simp add: wf_ctxt1_def apply_key_to_ref_def rev_apply_def)
       apply(force)


     (* frm' = Frm_L leaf_frame_ext - easy case? *)
     apply(rename_tac lf)
     apply(simp)
     apply(thin_tac "fs0 = ?x")
     apply(thin_tac "frm' = ?x")
     apply(thin_tac "x=?x")
     (* we have got to a leaf, and at frm' we return Fs_r *)
     apply(subgoal_tac "? fsr'.  \<lparr>fsr_r = r0, fsr_v = key_to_v lf k0\<rparr> = fsr'")
      prefer 2 apply(force)
     apply(erule exE)
     apply(simp)
     apply(subgoal_tac "? v'. key_to_v lf k0 = v'")
      prefer 2 apply(force)
     apply(erule exE)
     apply(simp add: fs_step_invariant_def)
     apply(drule_tac t="fs'" in sym)
     apply(simp)
     apply(thin_tac "fs' = ?x")
     apply(drule_tac t="fsr'" in sym)
     apply(simp)
     apply(thin_tac "fsr' = ?x")
     apply(simp)
     apply(simp (no_asm) add: rev_apply_def)
     apply(simp add: page_ref_key_to_v_def)
     (* page_ref_to_map could be none or some *)
     apply(subgoal_tac "? m0. (page_ref_to_map (ctxt_p2f_t.truncate ctxt1) s0 r0 n0) = m0")
      prefer 2 apply(force)
     apply(erule exE)
     apply(simp)
     apply(case_tac m0)
      (* m0 = None *)
      apply(simp)
      (* the map at r0 is none ; but we have a leaf frame; contradiction; FIXME the following should be simplified *)
      (*
      apply(simp add: page_ref_to_frame_def)
      apply(case_tac "ref_to_page s0 r0") apply(force)
      apply(simp)
      apply(rename_tac p0)
      *)
      (*  ref_to_page s0 r0 = Some p0 *)
      apply(simp add: page_ref_to_map_def)
      apply(case_tac "page_ref_to_kvs (ctxt_p2f_t.truncate ctxt1) s0 r0 n0") 
       (* page_ref_to_kvs = none *)
       apply(simp)
       (* apply(simp add: ref_to_page_def) *)
       apply(simp add: page_ref_to_kvs_def)
       apply(simp add: rev_apply_def)
       apply(case_tac "page_ref_to_tree (ctxt_p2f_t.truncate ctxt1) s0 r0 n0")
        (* page_ref_to_tree (ctxt_p2f_t.truncate ctxt1) s0 r0 n0 = none *)
        (* page_ref_to_tree defined by primrec *)
        apply(case_tac n0)
         apply(force)
         (*
         apply(simp)
         apply(simp add: page_ref_to_frame_def)
         apply(force simp add: ref_to_page_def rev_apply_def)
         *)

         (* n0 = suc nat *)
         apply(rename_tac n0')
         apply(simp)
         apply(simp add: page_ref_to_frame_def)
         apply(simp add: ref_to_page_def rev_apply_def)
         apply(case_tac "dest_store s0 r0") apply(force) apply(simp)
         apply(rename_tac p0)
         (* this case should be impossible because n0 was not 0, but we got a leaf ; by wf of store; sledgehammer should get this *)
         apply(simp add: wf_store_def wf_store_page_ref_to_map_def)
         apply(erule conjE)
         apply(erule exE)
         apply(rename_tac m2)
         apply(simp add: page_ref_to_map_def page_ref_to_kvs_def Let_def)
         apply(simp add: find_state_to_page_ref_def page_ref_to_frame_def)
         apply(simp add: ref_to_page_def)
         apply(simp add: rev_apply_def)
         apply(force simp add: rresult_to_option_def)  (* sledgehammer should get this *)
        (* end page_ref_to_tree (ctxt_p2f_t.truncate ctxt1) s0 r0 n0 = none *)

        (* page_ref_to_tree = Some a *)
        apply(rename_tac t0)
        apply(case_tac n0)
         apply(force)

         (* n0 = suc nat *)
         apply(rename_tac n0')
         apply(force)

       (* page_ref_to_kvs = Some a *)
       apply(rename_tac kvs)
       apply(simp)
       (* but m0 = none, so can't have kvs = some *)
       apply(force simp add:rev_apply_def)

      (* m0 = some a *)
      apply(rename_tac m1)
      apply(simp)
      apply(thin_tac "m0 = ?x")
      apply(simp)
      apply(simp add: page_ref_to_map_def)
      apply(simp add: rev_apply_def)
      apply(elim exE conjE)
      apply(simp add: page_ref_to_kvs_def rev_apply_def)
      apply(case_tac n0)
       (* 0 *)
       apply(simp)
       apply(simp add: rev_apply_def)
       apply(simp add: kvs_to_map_def)
       apply(drule_tac t=z in sym)
       apply(simp)
       apply(thin_tac "z=?x")
       apply(subgoal_tac "fsl = (| fsl_k = k0, fsl_r = r0 |)") prefer 2 apply(force)
       apply(simp)
       apply(simp add:page_ref_to_frame_def)
       apply(case_tac "ref_to_page s0 r0") apply(force)
       apply(rename_tac p0)
       apply(simp)
       apply(simp add: ref_to_page_def)
       apply(subgoal_tac "? kvs. lf = (| lf_kvs=kvs |)") prefer 2 apply (metis leaf_frame.cases)  
       apply(elim exE)
       apply(simp)
       apply(thin_tac "lf=?x")
       apply(thin_tac "fsl=?x")
       apply(thin_tac "n0=0")
       apply(clarsimp)
       apply(force simp add: key_to_v_def rev_apply_def tree_to_kvs_def)

       (* suc - should be a contradiction with leaf frame *)
       apply(rename_tac n0')
       apply(force)
  done

end