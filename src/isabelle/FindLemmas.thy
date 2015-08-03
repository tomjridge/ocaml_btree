theory "FindLemmas" 

imports 
 	 Main "~~/src/HOL/Library/Code_Target_Numeral"
	 "../../src_ext/lem/isabelle-lib/Lem_pervasives" 
	 "../../src_ext/lem/isabelle-lib/Lem_set_extra" 
	 "../../src_ext/lem/isabelle-lib/Lem_assert_extra" 
	 "gen_isabelle/Btree"
	 "PreludeLemmas"
begin

(* find does not alter the store, 
returns a page id in the store and the corresponding entry key is the input *)

lemma norm_find_h_is_correct:
"\<forall> env s r n k p i es. norm_find_h env ((Some(Find k)),r,s) h = (Some(p,i),s) \<longrightarrow> (p \<in> dom s) 
\<and> (case (s p) of (Some(LNode(L(es)))) \<Rightarrow> (case (nth_from_1 es i) of Some e \<Rightarrow> (e \<in> set es) \<and> (k = (entry_to_key env e)) | _ \<Rightarrow> False) | _ \<Rightarrow> False)"
apply (simp add:norm_find_h_always_return_page_id_in_store)
apply auto
apply (induct h)
  (*h = 0 *)
  apply (simp add:norm_find_h.simps find_trans_def)
  apply (case_tac "s r")
    apply auto

    apply (case_tac a)
      apply (case_tac inode)
      apply auto
      apply (case_tac "first aa (key_lt0 env k)")
            apply (case_tac b)
              apply auto

              apply (case_tac "nth_from_1 b a")
              apply auto

      apply (case_tac lnode)
      apply (case_tac "first list (\<lambda>x. k = entry_to_key env x)")
        apply auto

        apply (simp add:first_def)
        apply (case_tac "find_indices (\<lambda>x. k = entry_to_key env x) list")
          apply auto

    (*h = 0 *)
  apply (simp add:norm_find_h_simps find_trans_def)
  apply (case_tac "s r")
    apply auto

    apply (case_tac a)
      apply (case_tac inode)
      apply auto
      apply (case_tac "first aa (key_lt0 env k)")
            apply (case_tac b)
              apply auto

              apply (case_tac "nth_from_1 b a")
              apply auto

      apply (case_tac lnode)
      apply (case_tac "first list (\<lambda>x. k = entry_to_key env x)")
        apply auto

        apply (simp add:norm_find_h.simps)
          apply (case_tac h)
            apply auto
            apply (simp add:find_trans_def)
done

lemma find_h_is_correct [simp]:
"\<forall> env s r n k p i es. find_h env ((Some(Find k)),r,s) h = (Some(p,i),s) \<longrightarrow> (p \<in> dom s) 
\<and> (case (s p) of (Some(LNode(L(es)))) \<Rightarrow> (case (nth_from_1 es i) of Some e \<Rightarrow> (e \<in> set es) \<and> (k = (entry_to_key env e)) | _ \<Rightarrow> False) | _ \<Rightarrow> False)"
apply (simp add:find_h_def)
apply (case_tac h)
  apply (simp_all add:norm_find_h_is_correct)
done

(* find_entry behaves as a map lookup *)

lemma sub :
"norm_wf_btree env s (r,set all_entries,n) h \<Longrightarrow> \<not> (Set.is_empty (set all_entries))"
sorry

lemma norm_find_entry_equal_to_map_lookup_if_wf_btree:
"\<forall> (* env k s *) r .
let all_entries = (case (norm_entries_list_h s r h) of (Some list) \<Rightarrow> list | None \<Rightarrow> []) in
norm_wf_btree env s (r,set all_entries,n) h \<longrightarrow> 
(find_entry (norm_find_h env (Some(Find k),r,s) h) = 
(map_of (map (\<lambda> e . (entry_to_key env e,e)) all_entries) k))"
apply (simp add:map_and_listfind_equal)
apply (induct h, auto)
 (* 0 *)
 apply (simp add:norm_find_h.simps find_trans_def)
 apply (case_tac "s r")
  apply (simp add:find_entry.simps norm_entries_list_h.simps)

  apply (case_tac a)
   apply (case_tac inode)
   apply auto

   apply (case_tac lnode)
   apply simp
    apply (case_tac "first list (\<lambda>x. k = entry_to_key env x)")
    apply (simp add:nth_first_is_list_find_simp find_entry.simps norm_entries_list_h.simps )

    apply (simp add:nth_first_is_list_find_simp find_entry.simps norm_entries_list_h.simps )
    
  (* Suc *)
  (* these are the steps of the proof:
  - show that the list is ordered (solving the conditions of wf_btree)
  - bring the rec-clause from a List.all to a singular
    (this should be something like: we are interested only in descending the same subtree norm_entries_list_h descends)
  - show that with an ordered list, List.find .. h = List.find .. Suc h
  *)
  apply (case_tac "s r")
   (* None *)
   apply simp

   (*Some a*)
   apply (case_tac a)
   defer
    (* a = lnode *)
    apply simp

    (* a = inode *)
    apply (case_tac inode)
    apply (case_tac prod)
    apply simp
    apply (case_tac "n \<noteq> length b")
     (*n \<noteq> length b*)
     apply simp

     (*n = length b*)
     apply simp
     apply (case_tac "Suc (length aa) \<noteq> length b")
     (*Suc (length aa) \<noteq> length b*)
      apply simp

     (*Suc (length aa) = length b*)
      apply (case_tac "aa")
       (* aa = [] *)
       apply simp

       (* aa \<noteq> [] *)
       apply (simp add:Let_def)
       (*now we try to show that the list of entries must be ordered *)
       (* union_clause : 
        we know that ss is norm_entries_list_h and it is not None *)
       apply (case_tac "norm_entries_list_h s r (Suc h)")
        (* norm_entries_list_h s r (Suc h) = None *)
        apply simp

        (* norm_entries_list_h s r (Suc h) = Some list *)
        apply simp
        (* cond_mj *)
        apply (case_tac "\<forall>j\<in>set (from_to (Suc 0) (length b)). 
          case case nth_from_1 b j of None \<Rightarrow> None | Some x \<Rightarrow> get_m s x of None \<Rightarrow> False | Some x \<Rightarrow> minN env \<le> x")
        defer
         (* cond_mj = False*)
         apply simp

         (* cond_mj = True*)
         apply simp
         (* now we solve cond_s1: we know that the first subtree has the smallest keys *)
         apply (case_tac "index b 0")
          (* index b 0 = None *)
          apply simp

          apply simp
          apply (case_tac "norm_entries_list_h s (b ! 0) h")
           (* norm_entries_list_h s (b ! 0) h = None *)
           apply simp

           (* norm_entries_list_h s (b ! 0) h = Some ae *)
           apply simp
           apply (case_tac "\<forall>s\<in>set ae. key_lt0 env (entry_to_key env s) ab")
           defer
            (*\<forall>s\<in>set ae. key_lt env (entry_to_key env s) ab = False *)
            apply simp

            (*\<forall>s\<in>set ae. key_lt env (entry_to_key env s) ab*)
            apply simp
            (* cond_sn: we know that the last subtree has the biggest keys*)
            apply (case_tac "nth_from_1 (ab # list) (length b - Suc 0)")
             apply simp

             apply simp
             apply (case_tac " nth_from_1 b (length b)")
              apply simp

              apply simp
              apply (case_tac "norm_entries_list_h s ag h")
               (* norm_entries_list_h s ag h = None *)
               apply simp

               (*norm_entries_list_h s ag h = Some ah*)
               apply simp
               apply (case_tac "(\<forall>s\<in>set ah. key_lte env af (entry_to_key env s))")
               defer
                (*not \<forall>s\<in>set ah. key_lte env af (entry_to_key env s)*)
                apply simp

                (*\<forall>s\<in>set ah. key_lte env af (entry_to_key env s)*)
                apply simp
                (* cond_sj : we know that all the subtrees have keys in increasing order*)
                apply (case_tac " \<forall>j\<in>set (from_to (Suc 0) (length b - 2)). \<exists> qi . index b j = Some qi")
                defer
                 apply simp
                 apply force

                 (* \<forall>j\<in>set (from_to (Suc 0) (length b - 2)). \<exists> qi . index b j = Some qi *)
                 apply simp
                 apply (case_tac "\<forall>j\<in>set (from_to (Suc 0) (length b - 2)). \<exists> sl . norm_entries_list_h s (b ! j) h = Some sl")
                 defer
                  apply simp
                  apply force

                  (* \<forall>j\<in>set (from_to (Suc 0) (length b - 2)). \<exists> l . norm_entries_list_h s (b ! j) h = Some l *)
                  apply clarsimp
                  apply(subgoal_tac " \<forall>j\<in>set (from_to (Suc 0) (length ba - 2)).\<forall> sl.  (norm_entries_list_h s (ba ! j) h = Some sl) \<longrightarrow>
       (\<forall>s\<in>set sl. key_lte env a (entry_to_key env s)) \<and> (\<forall>s\<in>set sl. key_lt env (entry_to_key env s) ((ab # list) ! j))")
                   prefer 2
                   apply(rule)
                   apply(rule)
                   apply(rule)
                   apply(subgoal_tac " \<exists>sl. norm_entries_list_h s (ba ! j) h = Some sl")
                    prefer 2
                    apply(force)
                   apply(erule exE)
                   apply(erule_tac x=j in ballE) back back back back
                   apply(simp)
                   apply (case_tac "nth_from_1 (ab # list) j")
                    (* nth_from_1 (ab # list) j = None*)
                    apply simp

                    (* nth_from_1 (ab # list) j = Some*)
                    apply simp
                    apply (case_tac "index (ab # list) j")
                     apply simp

                     
                  apply clarify

oops

lemma nth_from_1_belong:
"nth_from_1 xs x = Some e \<longleftrightarrow> (e \<in> set xs \<and> (nth xs  (x - 1) = e) \<and> (x > 0))"
apply auto
 apply (case_tac x)
  apply simp+

 apply (case_tac x)
  apply simp+

 apply (case_tac x)
  apply simp+

 apply (induct xs)
  apply simp

  apply auto
   apply (case_tac x)
    apply simp

    apply simp
sorry

lemma norm_wf_btree_and_list_find:
"let all_entries = (case (norm_entries_list_h s r h) of (Some list) \<Rightarrow> list | None \<Rightarrow> []) in
h = Suc h' \<longrightarrow>
s r = Some (INode(I(aa,ba))) \<longrightarrow>
norm_wf_btree env s (r,set all_entries,n) h \<longrightarrow>
(first aa (key_lt env k) = None \<longrightarrow> 
(List.find (\<lambda>x. k = entry_to_key env x) (the (norm_entries_list_h s r (Suc h')))) = 
(List.find (\<lambda>x. k = entry_to_key env x) (the (norm_entries_list_h s (ba ! ((length ba) - (Suc 0)))  h')))
)
\<and>
(first aa (key_lt env k) = Some a \<longrightarrow>
((List.find (\<lambda>x. k = entry_to_key env x) (the (norm_entries_list_h s r (Suc h')))) = 
(List.find (\<lambda>x. k = entry_to_key env x) (the (norm_entries_list_h s (ba ! a)  h')))
))
"
apply clarsimp
apply (case_tac h)
apply force

(*let's do the initial work with wf_btree *)
apply clarsimp
apply (case_tac "n \<noteq> length ba")
 (*n \<noteq> length ba*)
 apply simp

 (*n = length b*)
  apply simp
  apply (case_tac "Suc (length aa) \<noteq> length ba")
   (*Suc (length aa) \<noteq> length b*)
   apply simp

   (*Suc (length aa) = length b*)
   apply (case_tac "aa")
    (* aa = [] *)
    apply simp

    (* aa \<noteq> [] *)
    apply (simp add:Let_def)
    (* now we can start working with our proof *)
    
    apply rule
     (* (first (a # list) (key_lt env k) = None \<longrightarrow>
        (\<forall>n. n < length ba - Suc 0 \<and> List.find (\<lambda>x. k = entry_to_key env x) (the (norm_entries_list_h s (ba ! n) (Suc nat))) = None)) *)
     apply clarsimp
     (* this subgoal should be true for cond_sn: indeed, we use key_lte *)
     apply (case_tac "nth_from_1 (a # list) (length ba - Suc 0)")
      apply clarsimp

      (* nth_from_1 (a # list) (length ba - Suc 0) = Some aaa *)
      apply clarsimp
      apply (case_tac "nth_from_1 ba (length ba)")
       apply clarsimp

       (* nth_from_1 ba (length ba) = Some ab *)
       apply clarsimp
       apply (case_tac "norm_entries_list_h s ab h'")
        apply clarsimp

        apply clarsimp
        apply (simp add:key_lte_def key_lt0_def norm_entries_list_h_simps)
         apply rule
        
        (*it seems I cannot prove anything unless I have a concrete definition of key_lt: 
        I cannot prove that the sublists of entries are ordered*)
        

         
     apply (force intro:sorry_fixme)

     (* \<forall>aa. first (a # list) (key_lt env k) = Some aa \<longrightarrow>
            (\<forall>n. n < aa \<and> List.find (\<lambda>x. k = entry_to_key env x) (the (norm_entries_list_h s (ba ! n) (Suc nat))) = None) *)
     apply clarsimp
     (* this subgoal should be true for cond_sj*)
     apply (force intro:sorry_fixme)
oops

lemma norm_find_entry_equal_to_map_lookup [simp]:
"\<forall> (* env k s *) r .
let all_entries = (case (norm_entries_list_h s r h) of (Some list) \<Rightarrow> list | None \<Rightarrow> []) in
find_entry (norm_find_h env (Some(Find k),r,s) h) = 
(map_of (map (\<lambda> e . (entry_to_key env e,e)) all_entries) k)"
apply (simp add:map_and_listfind_equal)
apply (induct h, auto)
  (* 0 *)
  apply (simp add:norm_find_h.simps find_trans_def)
  apply (case_tac "s r")
    apply (simp add:find_entry.simps norm_entries_list_h.simps)

    apply (case_tac a)
      apply (case_tac inode)
      apply auto
      apply (case_tac "first aa (key_lt0 env k)")
        apply (case_tac b)
        apply (simp add:find_entry.simps norm_entries_list_h.simps)

        apply (simp add:find_entry.simps norm_entries_list_h.simps)

        apply auto
        apply (case_tac "nth_from_1 b a")
          apply auto
          apply (simp add:find_entry.simps norm_entries_list_h.simps)

          apply (simp add:find_entry.simps norm_entries_list_h.simps)

      apply (case_tac lnode)
        apply auto
        apply (case_tac "first list (\<lambda>x. k = entry_to_key env x)")
          apply (simp add:find_entry.simps norm_entries_list_h.simps nth_first_is_list_find_simp)

          apply (simp add:find_entry.simps norm_entries_list_h.simps nth_first_is_list_find_simp)

  (* Suc *)
  apply (simp add:norm_find_h_simps find_trans_def)
  apply (case_tac "s r")
    (* s r = None *)
    apply (simp add:find_entry.simps norm_entries_list_h_simps)

    (* s r = Some a *)
    apply (case_tac a)
    defer
      apply (case_tac lnode)
      apply auto
      apply (case_tac "first list (\<lambda>x. k = entry_to_key env x)")
        apply (simp add:find_entry.simps)
        apply (simp add:norm_entries_list_h_simps first_def)

        apply (case_tac h)
          apply (simp add:norm_find_h.simps find_trans_def find_entry.simps)
          apply (simp add:norm_entries_list_h.simps first_def)

          apply (simp add:norm_find_h_simps find_trans_def find_entry.simps)
          apply (simp add:norm_entries_list_h.simps first_def)
 
      (* a = Inode inode *)
      apply (case_tac inode)
      apply (case_tac prod)
      apply clarsimp
      apply (case_tac "ba = []")
       apply simp
       apply (case_tac "first aa (key_lt0 env k)")
        apply (simp add:find_entry.simps norm_entries_list_h_simps)
        
        apply (simp add:find_entry.simps norm_entries_list_h_simps nth_from_1_def)
        apply (case_tac a)
         apply (simp add:add:find_entry.simps)+
      (* s r = Some (INode (I (aa, b))) *)
      (*we need wf_btree because we need to know the relation between keys and entries*)
       apply (subgoal_tac "(first aa (key_lt0 env k) = None \<longrightarrow> 
(List.find (\<lambda>x. k = entry_to_key env x) (the (norm_entries_list_h s r (Suc h)))) = 
(List.find (\<lambda>x. k = entry_to_key env x) (the (norm_entries_list_h s (ba ! ((length ba) - (Suc 0)))  h)))
)
\<and>
(\<forall> a. first aa (key_lt0 env k) = Some a \<longrightarrow>
((List.find (\<lambda>x. k = entry_to_key env x) (the (norm_entries_list_h s r (Suc h)))) = 
(List.find (\<lambda>x. k = entry_to_key env x) (the (norm_entries_list_h s (ba ! a)  h)))
))")  
      apply clarify
      apply (case_tac "first aa (key_lt0 env k)")
       apply simp
       apply (case_tac " nth_from_1 ba (length ba)")
        apply simp

        apply (simp add:find_entry.simps nth_from_1_def)
        apply (case_tac "length ba")
         apply simp
         (* blabla ... with this assumption the subgoals are true*)
        
       

       
sorry

lemma find_entry_equal_to_map_lookup:
"\<forall> env k c s r .
let all_entries = (case (entries_list_h s r h) of (Some list) \<Rightarrow> list | None \<Rightarrow> []) in
find_entry (find_h env (Some(Find k),r,s) h) = 
(map_of (map (\<lambda> e . (entry_to_key env e,e)) all_entries) k)"
apply (case_tac h)
apply (simp add:find_h_def find_entry.simps entries_list_h.simps first_def)


apply (simp add:find_h_def  entries_list_h.simps)
done


end
