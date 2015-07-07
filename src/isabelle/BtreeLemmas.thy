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
        apply (case_tac "nth_from_1 b (case first a (key_lt env k) of None \<Rightarrow> length b | Some i \<Rightarrow> i)")
          apply auto

          apply (case_tac lnode)
          apply auto
          apply (case_tac "first list (\<lambda>x. k = entry_to_key env x)")
          apply auto
          apply (simp add:first_def)
          apply (case_tac "find_indices (\<lambda>x. k = entry_to_key env x) list")
            apply auto
done
          
lemma find_entry_equal_to_map_lookup:
"\<forall> env k c s r. 
let n = case s r of Some(LNode(L(es))) \<Rightarrow> (length es) | Some(INode(I(_,es))) \<Rightarrow> (length es) | _ \<Rightarrow> 0 in
wf_btree env s (r, set(entries_list_h s r h),n) h \<longrightarrow>
find_entry (find_h env (Some(Find k),r,s) h) = 
(map_of (map (\<lambda> e . (entry_to_key env e,e)) (entries_list_h s r h)) k)"
apply (induction h rule:wf_btree.induct)
  (* h = 0 *)
  apply auto

  (* h = 1 *)
  apply (case_tac "s r")
    apply auto

    (* s r = Some a *)
    apply (case_tac a)
      (* a = INode *)
      apply (simp add:entries_list_h.simps)
      
      (* a = LNode *)
      apply (case_tac lnode)
        apply auto
        apply (case_tac "length list \<le> maxN env")
          apply auto

          apply (simp add:find_h_simps)
          apply (simp add:find_trans_def)
          apply (simp add:entries_list_h.simps)
            apply (case_tac "first list (\<lambda>x. k = entry_to_key env x)")
              apply (simp add:find_entry.simps)

              apply (simp add:find_entry.simps entries_list_h.simps)
        
  (* h = Suc *)
  apply (case_tac "s ra")
    apply auto

    (* s ra = Soma a*)
    apply (case_tac a)
      apply auto
      
      (* a = inode *)
      apply (case_tac inode)
      apply auto
      apply (case_tac "Suc (length a) = length b")
        apply auto

        apply (case_tac "a")
          apply auto

          apply (simp add:Let_def)
          (* we start solving the easy conditions of wf_btree *)
          apply (case_tac "nth_from_1 (aa # list) (length b - Suc 0)")
            apply auto

            apply (case_tac "nth_from_1 b (length b)")
              apply auto

              apply (case_tac "index b 0")
                apply auto

                apply (simp add:from_to_def)
                apply (case_tac "length b - Suc 0")
                  apply auto

                  apply (case_tac "get_m s (b ! 0)")
                    apply auto

                    (* the inductive hypothesis is there: now we just need to solve the remaining conditions *)
                      
oops

lemma find_entry_equal_to_map_lookup1:
"\<forall> env k c s r .
find_entry (find_h env (Some(Find k),r,s) h) = 
(map_of (map (\<lambda> e . (entry_to_key env e,e)) (entries_list_h s r h)) k)"
apply (induct h)
  apply (simp add:find_h.simps find_entry.simps entries_list_h.simps first_def)

  apply (simp add:find_trans_def find_h_simps find_entry.simps)
  apply auto
  apply (case_tac "s r")
    apply (simp add:find_entry.simps entries_list_h_simps first_def)

    apply auto
    (* here we have s r = a : the INode case is the most interesting *)
    apply (case_tac a)
      apply auto
      apply (case_tac inode)
      apply auto
      
oops
end
