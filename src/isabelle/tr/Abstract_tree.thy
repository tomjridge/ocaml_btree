theory "Abstract_tree" 

imports 
 	 Main
begin

section "preliminaries"

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

definition rev_apply :: "'a => ('a => 'b) => 'b" (infixl "|>" 100) where
  "rev_apply x f = f x"

section "page, page_ref, store"

(* type vars: 'bs 'k 'r 'v *)

datatype 'bs page = Page 'bs (* bytes *)

datatype 'r page_ref = Page_ref 'r

definition dest_page_ref :: "'r page_ref => 'r" where
  "dest_page_ref r0 == (case r0 of Page_ref r => r)"

datatype ('r,'bs) store = Store "('r ~=> 'bs page)"  (* different to paper: we store actual bytes *)

definition dest_store :: "('r,'bs) store => ('r ~=> 'bs page)" where
  "dest_store s0 == (case s0 of Store f => f)"

definition ref_to_page :: "('r,'bs) store => 'r page_ref => 'bs page option" where
  "ref_to_page s0 r0 == (s0|>dest_store) (r0|>dest_page_ref)"


section "key and frame"


datatype 'k key = Key 'k

definition dest_key :: "'k key => 'k" where
  "dest_key k = (case k of Key k => k)"

record ('r,'k) node_frame = 
  nf_n :: "nat"
  nf_ks :: "nat => 'k key"
  nf_rs :: "nat => 'r page_ref"

record ('k,'v) leaf_frame = 
  lf_kvs :: "('k key * 'v) list" (* slightly different to paper - we store ks in tree *) 

datatype ('r,'k,'v) frame = Frm_I "('r,'k) node_frame" | Frm_L "('k,'v) leaf_frame"


section "page and frame"

(* interpretation of pages *)
datatype ('bs,'k,'r,'v) page_to_frame = P2f "'bs page => ('r,'k,'v) frame"  (* note that this forces that the page internally stores its type; this is not necessary, but is used by step_find *)

definition dest_p2f :: "('bs,'k,'r,'v) page_to_frame => 'bs page => ('r,'k,'v) frame" where
  "dest_p2f x = (case x of P2f f => f)"

(**********)
(* to convert a page_ref to a frame, lookup the page option and use the above *)
record  ('bs,'k,'r,'v) ctxt =
  ctxt_p2f :: "('bs,'k,'r,'v) page_to_frame"

(* from this point, we don't duplicate 0/Suc defns, to minimize # of defns *)
definition page_ref_to_frame :: "('bs,'k,'r,'v) ctxt => ('r,'bs) store =>  'r page_ref => ('r,'k,'v) frame option" where
  "page_ref_to_frame c0 s0 r0 == (
    case ref_to_page s0 r0 of
    None => None
    | Some p => (Some( (c0|>ctxt_p2f|>dest_p2f) p))
)"



section "tree"

datatype ('k,'v) tree = Tr_nd "(nat * (nat => 'k key) * (nat => ('k,'v) tree))" | Tr_lf "('k key * 'v) list"

type_synonym tree_height = nat


function tree_to_kvs :: "('k,'v) tree => ('k key *'v) list" where
  "tree_to_kvs (Tr_lf(kvs)) = kvs"
  | "tree_to_kvs (Tr_nd(n,ks,ts)) = ([0..<n] |> (List.map ts) |> (List.map tree_to_kvs) |> List.concat)"
apply (metis PairE tree.exhaust)
apply (metis tree.inject(2))
apply (metis tree.distinct(2))
by (metis prod.sel(1) prod.sel(2) tree.inject(1))


section "page_ref_to_tree, page_ref_to_map, page_ref_key_to_v"

(* NB this has an explicit n argument, whereas wfness gives us that we can just use page_ref_to_frame *)
fun page_ref_to_tree :: "('bs,'k,'r,'v) ctxt =>  ('r,'bs) store => 'r page_ref => tree_height => ('k,'v) tree option" where
  "page_ref_to_tree c0 s0 r0 0 = (
      case page_ref_to_frame c0 s0 r0 of 
      None => None 
      | Some frm => (
        case frm of 
        Frm_L(lf) => (Some(Tr_lf (lf|>lf_kvs)))
        | _ => impossible  (* impossible *)))"
  | "page_ref_to_tree c0 s0 r0 (Suc n') = (
    let n0 = (Suc n') in
      case page_ref_to_frame c0 s0 r0 of
      None => None
      |  Some frm => (
        case frm of 
        Frm_I(nf) => (
          let n = (nf|>nf_n) in
          let ks = (nf|>nf_ks) in
          let rs = (nf|>nf_rs) :: (nat => 'r page_ref) in
          let f0 = (% r. page_ref_to_tree c0 s0 r n') :: ('r page_ref => ('k,'v) tree option) in 
          case (! (m::nat). m < n --> m |> rs |> f0 |> is_Some)  of
          True => (Some(Tr_nd(n,ks,(% (m::nat). m |> rs |> f0 |> dest_Some))))
          | False => None)
        | _ => impossible  (* impossible *)))"

(* notice that this ideally belongs in section "page and frame" *)
definition page_ref_to_kvs ::  "('bs,'k,'r,'v) ctxt =>  ('r,'bs) store => 'r page_ref => tree_height => ('k key*'v) list option" where
  "page_ref_to_kvs c0 s0 r0 n0 == (
  (page_ref_to_tree c0 s0 r0 n0)
  |> (% x. case x of
    None => None
    | Some t => Some(tree_to_kvs t)))"

definition kvs_to_map :: "('k key*'v) list => ('k key ~=> 'v)" where
  "kvs_to_map kvs == (map_of kvs)"

definition page_ref_to_map :: "('bs,'k,'r,'v) ctxt =>  ('r,'bs) store => 'r page_ref => tree_height => ('k key ~=> 'v) option" where
  "page_ref_to_map c0 s0 r0 n0 == (page_ref_to_kvs c0 s0 r0 n0) |> (map_option kvs_to_map)"

definition page_ref_key_to_v :: "('bs,'k,'r,'v) ctxt => ('r,'bs) store => 'r page_ref => 'k key => tree_height => 'v option" where
  "page_ref_key_to_v ctxt s0 r0 k0 n0 == (
    let m0 = page_ref_to_map ctxt s0 r0 n0 in
    Option.bind m0 (% m. m k0))"




section "key_to_ref, key_to_v"

(* NB we need some properties of these functions for correctness *)
datatype ('bs,'k,'r,'v) key_to_ref = Key_to_ref "('r,'k) node_frame => 'k key => 'r page_ref" 
datatype ('bs,'k,'r,'v) key_to_v = Key_to_v "('k,'v) leaf_frame => 'k key => 'v option"  (* may be no such v *)

definition dest_key_to_ref :: "('bs,'k,'r,'v) key_to_ref => ('r,'k) node_frame => 'k key => 'r page_ref" where
  "dest_key_to_ref k2r == (case k2r of Key_to_ref f => f)"

definition dest_key_to_v :: "('bs,'k,'r,'v) key_to_v => ('k,'v) leaf_frame => 'k key => 'v option" where
  "dest_key_to_v k2v == (case k2v of Key_to_v f => f)"

(**********)
record  ('bs,'k,'r,'v) ctxt1 =  "('bs,'k,'r,'v) ctxt" +
  key_to_ref :: "('bs,'k,'r,'v) key_to_ref"
  key_to_v :: "('bs,'k,'r,'v) key_to_v"


section "find"

(* find *)
record ('bs,'k,'r,'v) find_state_l =
  fsl_k :: "'k key"
  fsl_r :: "'r page_ref"
(*   fnd0_s :: "('r,'bs) store" *)

record ('bs,'k,'r,'v) find_state_r =
  fsr_r :: "'r page_ref"
  fsr_v :: "'v option"
(*  fnd1_s :: "('r,'bs) store" *)

datatype ('bs,'k,'r,'v) find_state = Fs_l "('bs,'k,'r,'v) find_state_l" | Fs_r "('bs,'k,'r,'v) find_state_r"



definition fs_step :: "('bs,'k,'r,'v) ctxt1
  => (('r,'bs) store * ('bs,'k,'r,'v) find_state) 
  => (('r,'bs) store * ('bs,'k,'r,'v) find_state) option" where
  "fs_step ctxt1 s0fs0 == (
  let (s0,fs0) = s0fs0 in
  case fs0 of
  Fs_l fsl => (
    let r0 = (fsl|>fsl_r) in
    let k0 = (fsl|>fsl_k) in
    case (page_ref_to_frame (ctxt.truncate ctxt1) s0 r0) of 
    None => None
    | Some frm => (
      case frm of 
      Frm_I nf => (
        let k2r = ((ctxt1|>key_to_ref)|>dest_key_to_ref) in
        let r' = k2r nf k0 in
        Some(s0, Fs_l (fsl (| fsl_r := r' |))))
      | Frm_L lf => (
        let k2v = ((ctxt1|>key_to_v)|>dest_key_to_v) in
        let v = k2v lf k0 in
        Some(s0, Fs_r (| fsr_r = r0, fsr_v = v |)))))
  | Fs_r fsr => None)"

section "fs_step as a function"

text "iterate the fs_step function n times"

(* FIXME in the following we may want to use a standard isabelle while construction *)
definition fs_step_as_fun :: "('bs,'k,'r,'v) ctxt1 
  => tree_height
  => (('r,'bs) store * ('bs,'k,'r,'v) find_state) 
  => (('r,'bs) store * ('bs,'k,'r,'v) find_state)" where
  "fs_step_as_fun ctxt1 n0 s0fs0 == (
  let f0 = % x. x |> (fs_step ctxt1) |> dest_Some in
  (f0^^n0) s0fs0)"


section "wellformedness predicates"

(* FIXME obviously the following need to be filled in properly *)

definition wf_ctxt:: "('bs,'k,'r,'v) ctxt => bool" where
  "wf_ctxt ctxt == True"

definition wf_ctxt1:: "('bs,'k,'r,'v) ctxt1 => bool" where
  "wf_ctxt1 ctxt1 == True"

definition wf_store:: "('r,'bs) store => tree_height => bool" where
  "wf_store s0 n0 == True"



section "correctness of fs_step"

definition fs_step_invariant :: "('bs,'k,'r,'v) ctxt 
  => (('r,'bs) store * ('bs,'k,'r,'v) find_state)
  => tree_height
  => 'v option
  => bool" where
  "fs_step_invariant ctxt s0fs0 n0 v0 == (
    let (s0,fs0) = s0fs0 in
    case fs0 of
    Fs_l fsl => (
      let k0 = (fsl|>fsl_k) in
      let r0 = (fsl|>fsl_r) in
      let v' = page_ref_key_to_v ctxt s0 r0 k0 n0 in
      v' = v0)
    | Fs_r fsr => (
      let v' = (fsr|>fsr_v) in
      v' = v0))"

lemma FIXME: "P" sorry


lemma fs_step_is_invariant: "
  ! (ctxt1::('bs,'k,'r,'v) ctxt1) s0 fs0 n0 v0.
  wf_ctxt1 ctxt1 & wf_store s0 n0 
  --> (
  let ctxt = (ctxt.truncate ctxt1) in
  fs_step_invariant ctxt (s0,fs0) n0 v0 --> (
  let x = fs_step ctxt1 (s0,fs0) in
  case x of 
  None => True  (* if we are at a Fs_r, no further facts are available *)
  | Some (s',fs') => (
    (* n0 could be 0? but then fs' is Fs_r? *)
    fs_step_invariant ctxt (s',fs') (n0 - 1) v0)))"
  apply(rule)+
  apply(elim conjE)
  apply(subgoal_tac "? x. fs_step ctxt1 (s0, fs0) = x")
   prefer 2
   apply(force intro: FIXME)
  apply(erule exE)
  apply(simp add: Let_def)
  apply(rule)+
  apply(case_tac x)
   (* none *)
   apply(force)

   (* x = Some a *)
   apply(simp)
   apply(subgoal_tac "? s' fs'. a=(s',fs')")
    prefer 2
    apply(force intro: FIXME)
   apply(erule exE)+
   apply(simp)
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
   apply(case_tac " (page_ref_to_frame (ctxt.truncate ctxt1) s0 r0)")
    apply(force)

    (*  (page_ref_to_frame (ctxt.truncate ctxt1) s0 r0) = Some r' *)
    apply(rename_tac frm')
    apply(simp)
    apply(case_tac frm')
     (* r' = Frm_I node_frame_ext *)
     apply(rename_tac nf)
     apply(simp)
     apply(elim conjE)
     apply(drule_tac s=s0 in sym)
     apply(simp)
     apply(thin_tac "s' = s0")
     apply(subgoal_tac "? fsl'. (fsl\<lparr>fsl_r := (ctxt1 |> key_to_ref |> dest_key_to_ref) nf k0\<rparr>) = fsl'")
      prefer 2 apply(force)
     apply(erule exE)
     apply(simp)
     apply(subgoal_tac "? r'. (ctxt1 |> key_to_ref |> dest_key_to_ref) nf k0 = r'")
      prefer 2 apply(force)
     apply(erule exE)
     apply(thin_tac "a = ?x")
     apply(thin_tac "fs0 = ?x")
     apply(thin_tac "frm' = ?x")
     apply(thin_tac "x=?x")
     (* note how this goal is concise and readable *)
     apply(simp add: fs_step_invariant_def)
     apply(drule_tac t="fs'" in sym)
     apply(simp)
     apply(thin_tac "fs' = ?x")
     apply(drule_tac t="fsl'" in sym)
     apply(simp)
     apply(subgoal_tac "fsl\<lparr>fsl_r := r'\<rparr> = (| fsl_k = k0, fsl_r = r' |)") prefer 2 apply (metis (full_types) find_state_l.surjective find_state_l.update_convs(2) old.unit.exhaust rev_apply_def) 
     apply(thin_tac "fsl' = fsl\<lparr>fsl_r := r'\<rparr> ")
     apply(simp)
     apply(simp add: rev_apply_def)
     apply(simp add: page_ref_key_to_v_def)
     (* page_ref_to_map could be none or some *)
     apply(subgoal_tac "? m0. (page_ref_to_map (ctxt.truncate ctxt1) s0 r0 n0) = m0")
      prefer 2 apply(force)
     apply(erule exE)
     apply(simp)
     apply(case_tac m0)
      (* m0 = None *)
      apply(simp)
      (* FIXME this case ruled out by wellformedness *)
      apply(force intro: FIXME)

      (* m0 = Some a *)
      apply(rename_tac m1)
      apply(simp)
      apply(thin_tac "m0 = ?x")
      apply(subgoal_tac "? m0'.  (page_ref_to_map (ctxt.truncate ctxt1) s0 r' (n0 - Suc 0)) = m0'")
       prefer 2 apply(force)
      apply(erule exE)
      apply(simp)
      apply(case_tac "m0'")
       (* none - ruled out because m0 is_Some --> m0' is_Some *)
       apply(force intro: FIXME)

       (* m0' = Some a *)
       apply(rename_tac "m1'")
       apply(simp)
       apply(thin_tac "m0'=?x")
       (* m1 k0 = v0 --> m1' k0 = v0 ; this holds by wellformedness of key_to_ref *)
       apply(force intro:FIXME)


     (* r' = Frm_L leaf_frame_ext - easy case? *)


sorry

(*

     apply(subgoal_tac "(fsl' |> fsl_k) = k0 ") prefer 2 apply (metis find_state_l.cases find_state_l.select_convs(1) find_state_l.update_convs(2) rev_apply_def) 
     apply(simp)
     apply(subgoal_tac "(fsl' |> fsl_r) = r'") prefer 2 apply (metis find_state_l.cases find_state_l.select_convs(2) find_state_l.update_convs(2) rev_apply_def)
     apply()
     apply(thin_tac "fsl' = ?x")
     apply(simp)
     

     apply(simp add: page_ref_key_to_v_def)
     apply(case_tac v0)
      apply(simp)
     apply(simp add: Option.bind_def)
     
     
   
  
  apply(simp add: Let_def)

*)
  


(*
lemma correct_fs_step: "
  ! s0 fs0.
  let f0 = fs_step ctxt1 in
  
  "
*)


(*
locale l0 = 
  fixes r0:: "'r store_ref" 
  and s0:: "('a,'b,'r) store"
*)

end



(*


  let (s0,fs0) = s0fs0 in
  let P = (% x.
    let (f,n) = x in
    (f 0 = (s0,fs0)) 
    & (
    let (s1,fs1) = f n in
    case fs1 of Fs_l _ => False | Fs_r _ => True)
    & (! m. m < n --> (case (fs_step ctxt1 (f m)) of None => False | Some x => (x=f(Suc m)))))
  in 
  if (? fn. P fn) then
    let (f,n) = SOME fn. P fn in
    Some(f n)
  else
    None)
*)