theory "BtreeLemmas" 

imports 
 	 Main "~~/src/HOL/Library/Code_Target_Numeral"
	 "../../src_ext/lem/isabelle-lib/Lem_pervasives" 
	 "../../src_ext/lem/isabelle-lib/Lem_set_extra" 
	 "../../src_ext/lem/isabelle-lib/Lem_assert_extra" 
	 "gen_isabelle/Btree"
	 "PreludeLemmas"

begin

lemma find_h_is_correct [simp]:
"\<forall> env s r n k p i es. find_h env ((Some(Find k)),r,s) h = (Some(p,i),s) \<longrightarrow> (p \<in> dom s) 
\<and> (case (s p) of (Some(LNode(L(es)))) \<Rightarrow> (case (nth_from_1 es i) of Some e \<Rightarrow> (e \<in> set es) \<and> (k = (entry_to_key env e)) | _ \<Rightarrow> False) | _ \<Rightarrow> False)"
apply (simp add:find_h_def)
apply (case_tac h)
  apply auto
done

lemma find_entry_equal_to_map_lookup1:
"\<forall> env k c s r .
let all_entries = (case (entries_list_h s r h) of (Some list) \<Rightarrow> list | None \<Rightarrow> []) in
find_entry (find_h env (Some(Find k),r,s) h) = 
(map_of (map (\<lambda> e . (entry_to_key env e,e)) all_entries) k)"
apply (case_tac h)
apply (simp add:find_h_def find_entry.simps entries_list_h.simps first_def)


apply (simp add:find_h_def  entries_list_h.simps del:map_and_first_are_equal)
done

end
