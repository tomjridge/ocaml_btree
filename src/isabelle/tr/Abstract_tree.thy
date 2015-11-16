theory "Abstract_tree" 

imports 
 	 Main "~~/src/HOL/Library/Multiset" (* for size_change *)
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

definition frm_to_values_number :: "('r,'k,'v) frame \<Rightarrow> nat" where
  "frm_to_values_number frm = (case frm of Frm_I nf \<Rightarrow> (nf |> nf_n) + 1 | Frm_L lf \<Rightarrow> lf |> lf_kvs |> length)"

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
datatype ('bs,'k,'r,'v) key_to_ref = Key_to_ref "('r,'k) node_frame => 'k key => 'r page_ref" 
(* datatype ('bs,'k,'r,'v) key_to_v = Key_to_v "('k,'v) leaf_frame => 'k key => 'v option"  (* may be no such v *) - there is only one impl! *)

definition dest_key_to_ref :: "('bs,'k,'r,'v) key_to_ref => ('r,'k) node_frame => 'k key => 'r page_ref" where
  "dest_key_to_ref k2r == (case k2r of Key_to_ref f => f)"

(*
definition dest_key_to_v :: "('bs,'k,'r,'v) key_to_v => ('k,'v) leaf_frame => 'k key => 'v value_t option" where
  "dest_key_to_v k2v == (case k2v of Key_to_v f => f)"
*)

(**********)
record  ('bs,'k,'r,'v) ctxt_k2r_t =  "('bs,'k,'r,'v) ctxt_p2f_t" +
  key_to_ref :: "('bs,'k,'r,'v) key_to_ref"
(*  key_to_v :: "('bs,'k,'r,'v) key_to_v" *)


section "find, find_state, fs_step"

(* find *)
record ('bs,'k,'r,'v) find_state_l =
  fsl_k :: "'k key"
  fsl_r :: "'r page_ref"
(*   fnd0_s :: "('r,'bs) store" *)

record ('bs,'k,'r,'v) find_state_r =
  fsr_r :: "'r page_ref"
  fsr_v :: "'v value_t option"
(*  fnd1_s :: "('r,'bs) store" *)

datatype ('bs,'k,'r,'v) find_state = Fs_l "('bs,'k,'r,'v) find_state_l" | Fs_r "('bs,'k,'r,'v) find_state_r"

definition find_state_to_page_ref :: "('bs,'k,'r,'v) find_state => 'r page_ref" where
  "find_state_to_page_ref fs0 = (case fs0 of
    Fs_l fsl => (fsl|>fsl_r)
    | Fs_r fsr => (fsr |> fsr_r))"

definition fs_step :: "('bs,'k,'r,'v) ctxt_k2r_t
  => (('r,'bs) store * ('bs,'k,'r,'v) find_state) 
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
        let k2r = ((ctxt1|>key_to_ref)|>dest_key_to_ref) in
        let r' = k2r nf k0 in
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
  => (('r,'bs) store * ('bs,'k,'r,'v) find_state) 
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
& (dest_key_to_ref (key_to_ref ctxt1) nf k0 = r')
(* and the map exists at r' *)
& (page_ref_to_map ctxt s0 r' (n0 - Suc 0) = Some m1')
(* then the maps agree, at least for the key *)
& (m1 k0 = v0)
--> (m1' k0 = v0)
"


(*
definition wf_store_page_ref_to_map_none :: "('bs,'k,'r,'v) ctxt_k2r_t => ('r,'bs) store => tree_height => 'r page_ref => bool" where
  "wf_store_page_ref_to_map_none  c1 s0 n0 r0 == (
    let c0 = ctxt_p2f_t.truncate c1 in
    ((page_ref_to_map c0 s0 r0 n0 = None) --> False)
  )"
*)

definition wf_store_page_ref_to_map :: "('bs,'k,'r,'v) ctxt_k2r_t => ('r,'bs) store => tree_height => 'r page_ref => bool" where
  "wf_store_page_ref_to_map  c1 s0 n0 r0 == (
    let c0 = ctxt_p2f_t.truncate c1 in
(! m1 r' nf k0 . ((
(* if we have a map at r0 *)
(page_ref_to_map c0 s0 r0 n0 = Some m1)
& (page_ref_to_frame c0 s0 r0 = Some (Frm_I nf))
(* and we follow the key to r' *)
& (dest_key_to_ref (c1|>key_to_ref) nf k0 = r')
(* then we still have a map *)
& (page_ref_to_map c0 s0 r' (n0 - Suc 0) = None)
) --> False
))  (* FIXME does this follow from page_ref_to_map ~= None? FIXME isn't this a basic property of the defn of page_ref_to_map/page_ref_to_tree? *)
& (page_ref_to_map c0 s0 r0 n0 ~= None)    
  )"


definition wf_store:: "('bs,'k,'r,'v) ctxt_k2r_t => ('r,'bs) store => tree_height => 'r page_ref => bool" where
  "wf_store c1 s0 n0 r0 == (
(*    wf_store_page_ref_to_map_none c1 s0 n0 r0 *)
    wf_store_page_ref_to_map c1 s0 n0 r0

& True)"

(*

  

*)

section "correctness of fs_step"

definition fs_step_invariant :: "('bs,'k,'r,'v) ctxt_p2f_t
  => (('r,'bs) store * ('bs,'k,'r,'v) find_state)
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
     apply(subgoal_tac "? fsl'. (fsl\<lparr>fsl_r := (ctxt1 |> key_to_ref |> dest_key_to_ref) nf k0\<rparr>) = fsl'")
      prefer 2 apply(force)
     apply(erule exE)
     apply(simp)
     apply(subgoal_tac "? r'. (ctxt1 |> key_to_ref |> dest_key_to_ref) nf k0 = r'")
      prefer 2 apply(force)
     apply(erule exE)
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
       apply(simp add: page_ref_to_map_def page_ref_to_kvs_def rev_apply_def find_state_to_page_ref_def)
       apply(elim exE conjE)
       apply(simp)
       apply (metis option.distinct(1))  

       (* m0' = Some a *)
       apply(rename_tac "m1'")
       apply(simp)
       apply(thin_tac "m0'=?x")
       (* m1 k0 = v0 --> m1' k0 = v0 ; this holds by wellformedness of key_to_ref, and page_ref_to_map Suc *)
       apply(simp add: wf_ctxt1_def)
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
       apply(force simp add: key_to_v_def rev_apply_def)

       (* suc - should be a contradiction with leaf frame *)
       apply(rename_tac n0')
       apply(force)
  done

section "frame_to_page, ctxt_f2p"

(* encoding of pages *)
datatype ('bs,'k,'r,'v) frame_to_page = F2p "('r,'k,'v) frame \<Rightarrow> 'bs page"

definition dest_f2p :: "('bs,'k,'r,'v) frame_to_page => ('r,'k,'v) frame \<Rightarrow> 'bs page" where
  "dest_f2p x = (case x of F2p f => f)"

record ('bs,'k,'r,'v) ctxt_f2p_t = "('bs,'k,'r,'v) ctxt_k2r_t" +
  ctxt_f2p :: "('bs,'k,'r,'v) frame_to_page"
  
section "insert, insert_state, insert_step"

type_synonym 'r root_p_ref = "'r page_ref"

record ('bs,'k,'r,'v) ctxt_insert_t = "('bs,'k,'r,'v) ctxt_f2p_t" +
  maxNumValues  :: nat
  free_page_ref :: "('r,'bs) store \<Rightarrow> ('r page_ref * ('r,'bs) store)" (* need to constraint this so that the returned page_ref is not in the store *)
  (* I need an interface that alters Fr_I *)
  new_nf :: "('r,'k) node_frame"
  (*add_key_nf should update the nf_n field of the node_frame when key is Some *)
  add_key_page_ref_nf :: "('k key) option \<Rightarrow> 'r page_ref \<Rightarrow> ('r,'k) node_frame \<Rightarrow> ('r,'k) node_frame"
  (* [sust_page_ref_nf old new frm] substitute a given page_ref with another, if the first one is present *)
  subst_page_ref_nf :: "'r page_ref \<Rightarrow> 'r page_ref \<Rightarrow> ('r,'k) node_frame \<Rightarrow> ('r,'k) node_frame"

fun ins :: "('k * 'v) \<Rightarrow> ('k * 'v) list \<Rightarrow> ('k * 'v) list" where
  "ins kv [] = [kv]"
  | "ins kv (kv'#kvs) =
    (if (fst kv) = (fst kv')
    (* update entry *)
    then kv#kvs
    else kv'#(ins kv kvs))
  "

(* insert *)
record ('k,'r,'v) insert_state_t =
  ist_kv :: "('k key * 'v value_t)"
  ist_r  :: "'r page_ref"

datatype ('k,'r,'v) insert_state =
    Ist_root "('k,'r,'v) insert_state_t" (* case in which root is full and we create a new root *)
  | Ist_insert_nonfull "('k,'r,'v) insert_state_t"
  | Ist_done

definition split_child :: "('bs,'k,'r,'v) ctxt_insert_t
  => (('r,'bs) store * ('r page_ref * ('r,'k) node_frame) * ('r page_ref * ('r,'k,'v) frame)) 
  => (('r,'bs) store * ('r,'k) node_frame)" where
(* NB: having a node_frame in the result allows us to spare a READ to disk (although likely that data would be in the cache) *)
  "split_child ctxt c0 = (
  let (s0, (x_r,x_nf),(y_r,y_frm)) = c0 in
  (* we need to allocate 2 new nodes *)
  let (z_r,s0) = (ctxt |> free_page_ref) s0 in
  let (y_r',s0) = (ctxt |> free_page_ref) s0 in
  (* we substitute y_r with y_r' in x_nf*)
  let x_nf = (ctxt |> subst_page_ref_nf) y_r y_r' x_nf in    
  let f2p = ((ctxt_f2p_t.truncate ctxt) |> ctxt_f2p |> dest_f2p) in
  let add_kpr_nf = (ctxt |> add_key_page_ref_nf) in
  let ((x_r,x_nf'),(y_r',y_frm'),(z_r,z_frm)) = 
    (case y_frm of
    Frm_L y_lf \<Rightarrow>
      let kvs = y_lf |> lf_kvs in
      (* second half of the entries *)
      let kvs_2 = (drop ((length kvs) div 2) kvs) in
      (* first half of the entries *)
      let kvs_1 = (take ((length kvs) div 2) kvs) in
      (* FIXME likely I need to insert key and page_ref together in a frame to permit the right positioning of them *)  
      (* we update the parent node with z
      and we *copy* the median key (i.e. the first key of the kvs_2) of lf*)
      (* NB: if we are splitting nodes (in ist_step) they cannot be empty, so hd cannot be undefined *)
      let x_nf' = add_kpr_nf (Some (fst (hd kvs_2))) z_r x_nf in
      ((x_r,x_nf'),(y_r',(Frm_L \<lparr> lf_kvs = kvs_1 \<rparr>)),(z_r,(Frm_L \<lparr> lf_kvs = kvs_2 \<rparr>)))
    | Frm_I y_nf \<Rightarrow>
      let n  = (y_nf|>nf_n)  in
      let ks = (y_nf|>nf_ks) in
      let rs = (y_nf|>nf_rs) :: (nat => 'r page_ref) in
      let median_key = ks (n div 2) in
      (* we copy the largest keys and page_refs in the new node z, the median key is excluded though (it is going in the parent )*)
      let z_nf = add_kpr_nf None (rs ((n div 2)+1)) (ctxt |> new_nf) in
      let z_nf = foldl (% a n . (add_kpr_nf (Some (ks n)) (rs (n+1)) a) ) z_nf [(n div 2)+1..< n] in
      (* we delete the largest keys and page_refs from y (i.e. we create a new nf with the smallest keys) *)
      let y_nf' = add_kpr_nf (None) (rs 0) (ctxt |> new_nf) in
      let y_nf' = foldl (% a n . (add_kpr_nf (Some (ks n)) (rs (n+1)) a) ) y_nf' [0..<(n div 2)] in
      (* we update the parent node with z and the median_key *)
      let x_nf' = add_kpr_nf (Some median_key) z_r x_nf in
      ((x_r,x_nf'),(y_r',(Frm_I y_nf')),(z_r,(Frm_I z_nf))))
  in
  (* we update the store *)
  (* the new frame contains the second half of the old frame data *)
  let s1 = Store ((dest_store s0) (z_r \<mapsto> (f2p z_frm))) in
  (* the old frame contains the first half of the old frame data *)
  let s2 = Store ((dest_store s1) (y_r' \<mapsto> (f2p y_frm'))) in
  (* the parent frame got the median key and the new page_refs *)
  let s3 = Store ((dest_store s2) (x_r \<mapsto> (f2p (Frm_I x_nf')))) in
  (s3,x_nf'))"

definition ist_step :: "('bs,'k,'r,'v) ctxt_insert_t
  => (('r,'bs) store * 'r root_p_ref * ('k,'r,'v) insert_state) 
  => (('r,'bs) store * 'r root_p_ref * ('k,'r,'v) insert_state) option" where
  "ist_step ctxt s0ist0 = (
  let (s0,root,ist0) = s0ist0 in
  let ctxt_f2p_r = (ctxt_f2p_t.truncate ctxt) in
  let f2p = (ctxt_f2p_r |> ctxt_f2p |> dest_f2p) in
  let ctxt_k2r_r = ctxt_k2r_t.truncate ctxt_f2p_r in
  let k2r = ((ctxt_k2r_r|>key_to_ref)|>dest_key_to_ref) in
  let ctxt_p2f_r = ctxt_p2f_t.truncate ctxt_k2r_r in
  let add_kpr_nf = (ctxt |> add_key_page_ref_nf) in
  case ist0 of
    Ist_root ist \<Rightarrow>
    let r0 = (ist|>ist_r) in
    let (k0,v0) = (ist|>ist_kv) in
    (* new root page_ref to duplicate tree (we want to be able to build the old tree without the new entry after the insert) *)
    let (r0',s0) = (ctxt |> free_page_ref) s0 in
    (case (page_ref_to_frame ctxt_p2f_r s0 r0) of 
    None => (Error |> rresult_to_option)  (* invalid page access *)
    | Some frm => (
      case (frm_to_values_number frm = (ctxt |> maxNumValues)) of
       True \<Rightarrow>
       (* root is full, we need to create a new root *)
       let nf_r = (ctxt |> new_nf) in
       (* the old root node is a child *)
       let nf_r = add_kpr_nf None r0 nf_r in
       (* split_child updates the store with the new (page_ref, page)*)
       let (s1,_) = split_child ctxt (s0,(r0',nf_r),(r0,frm)) in
       Some (s1,r0',Ist_insert_nonfull(ist\<lparr> ist_r := r0'\<rparr>))
       | False \<Rightarrow>
       (* we need to duplicate the root in the store *)
       let s1 = Store ((dest_store s0) (r0' \<mapsto> (f2p frm))) in
       Some (s1,r0',Ist_insert_nonfull(ist\<lparr> ist_r := r0'\<rparr>))))
  | Ist_insert_nonfull ist \<Rightarrow>
    let r0 = (ist|>ist_r) in
    let (k0,v0) = (ist|>ist_kv) in
    (case (page_ref_to_frame ctxt_p2f_r s0 r0) of 
    None => (Error |> rresult_to_option)  (* invalid page access *)
    | Some frm => ( 
      case frm of
      Frm_L lf \<Rightarrow>
        (* in a leaf we just update the list of entries with the new one *)
        let frm' = Frm_L \<lparr> lf_kvs = ins (k0,v0) (lf |> lf_kvs) \<rparr> in
        (* and we update the store *)
        let s1 = Store ((dest_store s0) (r0 \<mapsto> (f2p frm'))) in
        Some (s1,root,Ist_done)
      | Frm_I nf \<Rightarrow>
        (* we need to find the child containing k0 *)
        let r' = k2r nf k0 in
        (* we resolve the child *)
        (case (page_ref_to_frame ctxt_p2f_r s0 r0) of
        None => (Error |> rresult_to_option)  (* invalid page access *)
        | Some child_frm => (
          case (frm_to_values_number child_frm = (ctxt |> maxNumValues)) of
          True \<Rightarrow>
            (* the child is full: we need to split it *)
            let (s1,nf') = split_child ctxt (s0,(r0,nf),(r',child_frm)) in
            (* split changed the parent frame, so we need to look for the child containing k0 again *)
            let r'' = k2r nf' k0 in
            Some (s1,root,Ist_insert_nonfull(ist\<lparr> ist_r := r''\<rparr>))
          | False \<Rightarrow>
          (** substitute r' with a new page_ref and substitute it with the  r' in the contents of r0*)
          let (r'',s0) = (ctxt |> free_page_ref) s0 in
          (* add a clone of the child (with a different page_ref) to the store *)
          let s1 = Store ((dest_store s0) (r'' \<mapsto> (f2p child_frm))) in
          (* update r0 contents with r'' instead of r' *)
          let frm' = (Frm_I ((ctxt |> subst_page_ref_nf) r' r'' nf)) in
          let s2 = Store ((dest_store s1) (r0 \<mapsto> (f2p frm'))) in
          Some (s2,root,Ist_insert_nonfull(ist\<lparr> ist_r := r''\<rparr>)))
       )))
  | Ist_done \<Rightarrow> (Error |> rresult_to_option))"  (* attempt to step Ist_done *)


section "correctness of ist_step"


end