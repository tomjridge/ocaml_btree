theory "BtreeLemmas" 

imports 
 	 Main "~~/src/HOL/Library/Code_Target_Numeral"
	 "../../src_ext/lem/isabelle-lib/Lem_pervasives" 
	 "../../src_ext/lem/isabelle-lib/Lem_set_extra" 
	 "../../src_ext/lem/isabelle-lib/Lem_assert_extra" 
	 "gen_isabelle/Btree"

begin

termination wf_btree by lexicographic_order
termination find_h by lexicographic_order

lemma btree_height_0_is_not_wf: " ((\<forall> e. \<forall> s. \<forall> c.  wf_btree e s c(( 0 :: nat)) \<longleftrightarrow> False))"
by auto

lemma find_trans_does_not_alter_store [simp]:
"(find_trans e (a,q,s)) = (b',q',s') \<Longrightarrow> s = s'"
(* cases of the given configuration *)
apply (case_tac "a")
  (* rewrite find_trans: with simp_all F_Ret case is solved*)
  apply (simp_all add:find_trans.simps)
  (* (Find(_),r,s) *)
  apply (case_tac "s q")
    (* None *)
    apply auto

    (* Some *)
    apply (case_tac "aa")
    apply auto
      (* Inode *)
      apply (case_tac "inode")
      apply auto

      (* Lnode *)
      apply (case_tac "lnode")
      apply auto
done

lemma find_h_simps: "
find_h env c (Suc h) = ( (
        (case  c of
          (F_Ret(p,n),_,s0) => (Some(p,n),s0)
        | (_,_,s0) =>
           (let c' = (find_trans env c) in
           find_h env c' ((Suc h)-(1::nat)))
        )))
"
  apply(force)
  done

(* the following definitions allow us to not unroll the find_h definition in the inductive case
  of find_h_does_not_alter_store *)
declare find_h.simps [simp del] 
declare find_h_simps [simp add]
lemma find_h_does_not_alter_store [simp]:
"\<forall> c0 p0 s0 opt s1. (find_h env (c0,p0,s0) h = (opt,s1)) \<longrightarrow> (s1=s0)"
apply (induct h)
  (* h = 0 *)
  apply(auto)
  apply (case_tac c0)

    (* c0 = Find  *)
    apply (simp add:find_h.simps)

    (* c0 = F_Ret *)
    apply (simp add:find_h.simps)
    
  (* h = Suc nat *)
  apply (case_tac c0)
  apply auto
  apply (simp add:find_trans.simps)
  apply (case_tac "s0 p0")
    (* s0 p0 = None *)
    apply auto

    (* s0 p0 = Some a *)
    apply (case_tac a)
      (* a = inode *)
      apply auto
      apply (case_tac inode)
      apply auto

      (* a = lnode *)
      apply (case_tac lnode)
      apply auto
done

end
