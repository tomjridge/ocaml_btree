theory "BtreeLemmas" 

imports 
 	 Main "~~/src/HOL/Library/Code_Target_Numeral"
	 "../../src_ext/lem/isabelle-lib/Lem_pervasives" 
	 "../../src_ext/lem/isabelle-lib/Lem_set_extra" 
	 "../../src_ext/lem/isabelle-lib/Lem_assert_extra" 
	 "gen_isabelle/Btree"
	 "PreludeLemmas"

begin

lemma find_h_does_not_alter_wf_btree1:
" (wf_btree env s0 (r,ss,n) h) \<and> find_h env (c0,r,s0) h = (Some(p,i),s) \<longrightarrow> (s = s0)"
apply auto
done

lemma find_h_is_correct:
"\<forall> env s r n k p i es. find_h env ((Some(Find k)),r,s) h = (Some(p,i),s) \<longrightarrow> (p \<in> dom s) 
\<and> (case (s p) of (Some(LNode(L(es)))) \<Rightarrow> (case (nth_from_1 es i) of Some e \<Rightarrow> True(*(e \<in> set es) \<and> (k = (entry_to_key env e))*) | _ \<Rightarrow> False) | _ \<Rightarrow> False)"
apply auto
  (* the page_id obtained by find is in the store *)
  apply (induct h)
    (* h = 0 *)
    apply (simp add:find_h.simps)

    (* h = Suc n*)
    apply (case_tac "s r")
      (* s r = None *)
      apply (simp add:find_h_simps find_trans_def)

      (* s r = Some *)
      apply (simp add:find_h_simps find_trans_def)
      apply (case_tac a)
        apply auto
        apply (case_tac inode)
        apply auto
        apply (case_tac "nth_from_1 b (case first a (key_lt env k) of None \<Rightarrow> length a + 1 | Some i \<Rightarrow> i)")
          apply auto

          apply (case_tac lnode)
          apply auto
          apply (case_tac "first list (\<lambda>x. key_eq env k (entry_to_key env x))")
          apply auto
          apply (simp add:first_def)
          apply (case_tac "find_indices (\<lambda>x. key_eq env k (entry_to_key env x)) list")
            apply auto
done

lemma find_entry_equal_to_map:
"\<forall> env k c h s r. 
let n = case s r of Some(LNode(L(es))) \<Rightarrow> (length es) | Some(INode(I(_,es))) \<Rightarrow> (length es) | _ \<Rightarrow> 0 in
wf_btree env s (r, (entry_set s r),n) h \<longrightarrow>
find_entry (find_h env (Some(Find k),r,s) h) = 
(map_of (foldl (\<lambda> acc l. case l of LNode(L(es)) \<Rightarrow> acc@(map (\<lambda> i. (entry_to_key env i,i)) es) | _ \<Rightarrow> acc) [] (list_of_set (Map.ran s)))) k"
(* the problem with this lemma is the h:
if it is smaller that the height of the tree the two operations behave differently*)
oops

end
