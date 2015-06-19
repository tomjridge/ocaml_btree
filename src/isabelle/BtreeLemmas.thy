theory "BtreeLemmas" 

imports 
 	 Main "~~/src/HOL/Library/Code_Target_Numeral"
	 "/home/andrea/workspace/lem/isabelle-lib/Lem_pervasives" 
	 "/home/andrea/workspace/lem/isabelle-lib/Lem_set_extra" 
	 "/home/andrea/workspace/lem/isabelle-lib/Lem_assert_extra" 
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

lemma find_trans_of_find_trans_does_not_alter_store [simp]:
"(find_trans e (find_trans e (a,q,s))) = (b',q',s') \<Longrightarrow> s = s'"
apply (case_tac "a")
apply auto
apply (simp add:find_trans.simps)
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

      apply (simp add:find_trans.simps)
done

lemma find_h_does_not_alter_store:
"(find_h e (a,r,s) h) = (a',b,s') \<Longrightarrow> s = s'"
apply (induct h)
apply auto
  (* h = 0 *)
  apply (case_tac "a")
  apply auto
  apply (case_tac " s aa")
  apply auto
  apply (case_tac " aaa")
  apply auto
  apply (case_tac "lnode")
  apply auto
  (* h = Suc h *)
oops
   
lemma find_does_not_alter_wfbtree: 
"(wf_btree e s (r,ss,n) h) \<Longrightarrow> (((find_h e ((Find k),r,s) h) = (i,q,s)) (*\<and> (if i = None then True else (the i \<in> ss \<and>  (key_lt e) k ((entry_to_key e) (the i))))*) )"
apply auto
apply (induction "h")
  (* h = 0 *)
  apply auto

  (* h = Suc h *)
  (* h again? Tried to use case_tac, but does not seem a good idea: cascade of cases *)
oops
end
