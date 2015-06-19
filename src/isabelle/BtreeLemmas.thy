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

lemma find_trans_does_not_alter_store1 [simp]:
"dest_find_config_store (find_trans e (a,q,s)) = s"
apply (case_tac a)
  (* a = Find*)
  apply (simp_all add:find_trans.simps)
  apply auto
  apply (case_tac "s q")
    apply auto
    (* s q = None *)
    apply (simp add: dest_find_config_store.simps)
    (* s q = Some aa *)
    apply (case_tac aa)
      (* aa = inode *)
      apply (case_tac inode)
      apply auto
      apply (simp add:dest_find_config_store.simps)
      (* aa = lnode *)
      apply (case_tac lnode)
      apply auto
      apply (simp add:dest_find_config_store.simps)
  (* a = F_Ret *)
  apply (simp add:dest_find_config_store.simps)
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

lemma find_trans_of_find_trans_does_not_alter_store1 [simp]:
"dest_find_config_store (find_trans e (find_trans e (a,q,s))) = s"
apply (case_tac "(find_trans e (a,q,s))")
apply (simp add:dest_find_config_store.simps)
apply (case_tac a)
apply (simp add:find_trans.simps)
apply auto
apply (case_tac "s q")
    (* None *)
    apply auto
    (* Some *)
    apply (case_tac "aaa")
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
"(wf_btree e s (r,ss,n) h) \<Longrightarrow> (\<lambda> (_,_,s'). s = s') (((find_h e ((Find k),r,s) h)) (*\<and> (if i = None then True else (the i \<in> ss \<and>  (key_lt e) k ((entry_to_key e) (the i))))*) )"
apply auto
apply (induction "h" rule:wf_btree.induct)
  (* h = 0 *)
  apply auto
  apply (case_tac "s0 ra")
    (* s0 ra = None *)
    apply auto
    (* s0 ra = Some ab *)
    apply (case_tac ab)
      (*ab=inode*)
      apply auto
      (*ab=lnode*)
      apply (case_tac lnode)
      apply auto
      apply (case_tac "n0 = length list \<and> n0 \<le> fanout env")
      apply auto
      apply (case_tac "ss0 = set list")
      apply auto
      apply (simp add:sorted_entry_list_def)
      apply auto
      apply (case_tac "list = []")
      apply auto
      apply (simp add:find_trans.simps)
      apply (case_tac "s0 r")
      apply auto
      apply (case_tac ab)
      apply auto
      apply (case_tac inode)
      apply auto
      apply (case_tac lnode)
      apply auto
      (* here we have a foldl: how to manage it? *)
      apply (case_tac "foldl
        (\<lambda>acc1 i.
            (case index (Btree.sort (entry_lt env) list) i of None \<Rightarrow> False
             | Some s_e \<Rightarrow>
                 case index list i of None \<Rightarrow> False | Some x \<Rightarrow> entry_eq env s_e x) \<and>
            acc1)
        True (from_to 0 (length list - Suc 0))")
      apply auto
      apply (simp add:find_trans.simps)
      apply (case_tac "s0 r")
      apply auto
      apply (case_tac "ab")
      apply auto
      apply (case_tac "inode")
      apply auto
      apply (case_tac "lnode")
      apply auto
      (* inductive step of recursion *)
      apply (case_tac va)
      apply auto
  (* h = Suc h *)
  
  (* h again? Tried to use case_tac, but does not seem a good idea: cascade of cases *)
oops
end
