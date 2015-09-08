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
      apply (case_tac "first aa (key_lt env k)")
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
      apply (case_tac "first aa (key_lt env k)")
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
    apply (simp add:cond_sn_def dd_def ss_def)
    apply clarsimp
     (* this subgoal should be true for cond_sn: indeed, we use key_lte *)
     apply (case_tac "nth_from_1 (a # list) (length ba - Suc 0)")
      apply clarsimp

      (* nth_from_1 (a # list) (length ba - Suc 0) = Some aaa *)
      apply (simp add:qq_def)
      apply clarsimp
      apply (case_tac "nth_from_1 ba (length ba)")
       apply clarsimp

       (* nth_from_1 ba (length ba) = Some ab *)
       apply clarsimp
       apply (case_tac "norm_entries_list_h s ((ba ! (length ba - Suc 0))) h'")
        apply clarsimp

        apply clarsimp
        apply (simp add:key_lte_def key_lt_def norm_entries_list_h_simps)
        apply rule
         apply clarsimp
         
        
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
      apply (case_tac "first aa (key_lt env k)")
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
     (* a = lnode *)
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
      apply auto
      (* s r = Some (INode (I (aa, b))) *)
      apply (case_tac "first a (key_lt env k)")
       (* first aa (key_lt env k) = None *)
       apply auto
       (* we know that nth_from_1 b (length b) is not None, unless b is [] *)
       apply(case_tac "b=[]")
        (* b cannot have length 0, by well-formedness *)
        (* let's try to prove without well-formedness *)
        apply(case_tac b, auto)
        apply (force simp add:find_entry.simps norm_entries_list_h_simps)

        (* b \<noteq> [] *)
        apply(case_tac " nth_from_1 b (length b)")
         (* ... = None *)
         apply(force simp add:nth_from_1_length)

         (* ... = Some a *)
         apply(simp)
         apply(simp add: norm_entries_list_h_simps)
         apply(rule)
          apply(rule)
          apply(subgoal_tac "\<exists>y. norm_entries_list_h s p h = Some y")
           prefer 2
            
           apply(subgoal_tac "p : set b")
            prefer 2
            apply(force intro: sorry_fixme)
           apply(force)
         apply(auto)

         

(* GOT TO HERE *)


        apply(simp add:  nth_from_1_length)

       apply(simp add: nth_from_1_length)
       apply(case_tac "nth_from_1 b (length b)")
        (*  nth_from_1 b (length b) = None *)
        apply(case_tac "b")
         apply(simp add: find_entry.simps)


       apply (case_tac b)
          (* b=[] *)
          apply (simp add:find_entry.simps norm_entries_list_h_simps)

          (* b = a # list *)
          apply (simp add: norm_entries_list_h_simps)
          apply auto
          (* it is necessary to show that find does not need to enter all the branches *)
            apply (case_tac "List.find (\<lambda>x. k = entry_to_key env x) y")
              apply auto
              apply (case_tac "norm_entries_list_h s ((a # list) ! length list) h")
                apply auto
                apply(case_tac "list")
                 apply(force)
                 apply(simp)
                 
(* THIS IS THE LNODE CASE, uncomment after INODE CASE is solved
      
*) 
oops

lemma norm_find_entry_equal_to_map_lookup:
"\<forall> (* env k s *) r .
(
wf_env env \<longrightarrow> norm_wf_btree env s (r,the(ss (Some r) s h),the(mm (Some r) s)) h \<longrightarrow> 
find_entry (norm_find_h env (Some(Find k),r,s) h) = 
(map_of (map (\<lambda> e . (entry_to_key env e,e)) (case (norm_entries_list_h s r h) of (Some list) \<Rightarrow> list | None \<Rightarrow> fail)) k))"
apply rule
apply (induct h)
 (* 0 *)
 apply (case_tac "s r")
  apply simp

  (* s r = Some a *)
  apply simp
  apply (case_tac a)
   apply simp

   (* a = lnode *)
   apply (case_tac lnode)
   apply (simp add:Let_def mm.simps get_m_def)
   apply (case_tac "length list > maxN env")
    apply simp

    (* length list \<le> maxN env *)
    apply (simp add:norm_find_h.simps find_trans_def ss.simps norm_entries_list_h.simps)
    apply (case_tac "first list (\<lambda>x. k = entry_to_key env x)")
      apply (simp add:find_entry.simps norm_entries_list_h.simps map_and_first_are_equal)

      apply (simp add:find_entry.simps norm_entries_list_h.simps map_and_first_are_equal)

 (* Suc h *)
 apply (case_tac "s r")
  apply simp

  (* s r = Some a *)
  apply (case_tac a)
  defer
   (* a = LNode *)
   apply simp

   (* a = INode*)
   apply (case_tac "inode")
   apply (case_tac prod)
   apply (simp add:Let_def del:norm_wf_btree.simps)
   apply (simp add:mm.simps get_m_def)
   apply (case_tac "Suc (length aa) \<noteq> length b")
    apply simp

    (*Suc (length aa) = length b*)
    apply simp
    apply (case_tac aa)
     apply simp

     (* aa = ab # list *) 
     apply (case_tac "b = []")
      apply simp
      
      (* b \<noteq> [] *)
      apply (simp add:Let_def norm_find_h_simps find_trans_def map_and_listfind_equal)
      (* we set the induction hypothesis we are going to use soon *)
      apply (subgoal_tac "s r = Some (INode(I(aa,b))) \<Longrightarrow>
        norm_wf_btree env s (r, the (ss (Some r) s (Suc h)), the (mm (Some r) s)) (Suc h) \<longrightarrow>
        (\<forall> i \<in> from_to (Suc 0) (length b). norm_wf_btree env s (b ! (i - Suc 0), the (ss (Some (b ! (i - Suc 0))) s h), the (mm (Some (b ! (i - Suc 0))) s)) h)")
      defer
       (* we solve the subgoal norm_wf_btree Suc h = norm_wf_btree h*)
       apply (simp add:norm_wf_btree_suc_n_then_norm_wf_btree_n)
       
      (*let's generalise and avoid the case split on first (ab#list) (key_lt env k) *)
      apply (subgoal_tac "\<exists>n. (case first (ab # list) (key_lt env k) of None \<Rightarrow> length b | Some i \<Rightarrow> i) = n")
      defer
       (* subgoal_tac "\<exists>n. (case first (ab # list) (key_lt env k) of None \<Rightarrow> length b | Some i \<Rightarrow> i) = n *)
       apply (simp add:first_def)

      apply (erule exE)
      apply (subgoal_tac "(case first (ab # list) (key_lt env k) of None \<Rightarrow> length b | Some i \<Rightarrow> i) = n \<longrightarrow> \<not> ((ab # list) = []) \<and> \<not>(n = 0) \<and> (n \<le> Suc (length (ab # list)))")
       defer
       (* subgoal_tac "(case first (ab # list) (key_lt env k) of None \<Rightarrow> length b | Some i \<Rightarrow> i) = n \<longrightarrow> \<not> ((ab # list) = []) \<and> \<not>(n = 0) \<and> (n \<le> Suc (length (ab # list))) *)
       apply (simp add:first_def find_index_def)
       apply (case_tac "key_lt env k ab")
        apply simp+

        apply (case_tac "map Suc (find_indices (key_lt env k) list) ")
         apply simp
           
         apply simp
         apply (subgoal_tac "\<forall>x \<in> set (find_indices (key_lt env k) list). Suc x \<le> length list \<and> length list < length b")
         apply force
          (* subgoal_tac "\<forall>x \<in> set (find_indices (key_lt env k) list). Suc x \<le> length list \<and> length list < length b" *)
          apply simp
      (* we proved the generalisation, we can proceed with the main proof*)

      apply simp
      apply (case_tac "nth_from_1 b n")
       apply simp

       (* nth_from_1 b n = Some ac *)
       apply (simp add:nth_from_1_def)
       apply (case_tac "n")
         apply simp+

         (* n = Suc nat *)
         apply (simp add:norm_entries_list_h_simps map_and_listfind_equal)
         (* we set the case in which norm_entries_list h = None as another subgoal *)
         apply rule
          apply (subgoal_tac "\<forall>i\<in>from_to (Suc 0) (length b).
           norm_wf_btree env s (b ! (i - Suc 0), the (ss (Some (b ! (i - Suc 0))) s h), the (mm (Some (b ! (i - Suc 0))) s)) h \<Longrightarrow>
           norm_wf_btree env s (b ! (n - Suc 0), the (ss (Some (b ! (n - Suc 0))) s h), the (mm (Some (b ! (n - Suc 0))) s)) h")
          apply (simp add: mm.simps get_m_def)
          apply (simp add:listfind_Suc_h_eq_listfind_h_if_ordered_keys)
          (* main goal solved *)

            (*subgoal: ((List.find (\<lambda>x. k = entry_to_key env x) (List.concat (map (the \<circ> (\<lambda>q. norm_entries_list_h s q h)) b)))
           =
           (List.find (\<lambda>x. k = entry_to_key env x) ((case (norm_entries_list_h s (b!(length b - Suc 0)) h) of None \<Rightarrow> [] | Some list \<Rightarrow> list) )))")*)
           apply (simp add:from_to_set)
           apply force
        
           (* (\<exists>x\<in>set ba. norm_entries_list_h s x h = None)*)
           (* this should falsify wf_btree, because no norm_entries_list_h call is allowed to return false *)
           apply (simp add:union_clause_def norm_entries_list_h_simps)
           apply force
done

lemma find_entry_equal_to_map_lookup:
"
(
wf_env env \<longrightarrow> wf_btree env s (r,the(ss (Some r) s (h-(1::nat))),the(mm (Some r) s)) h \<longrightarrow> 
find_entry (find_h env (Some(Find k),r,s) h) = 
(map_of (map (\<lambda> e . (entry_to_key env e,e)) (case (entries_list_h s r h) of (Some list) \<Rightarrow> list | None \<Rightarrow> fail)) k))
"
apply (case_tac h)
apply (simp add:find_h_def find_entry.simps entries_list_h.simps first_def wf_btree_def)

apply (simp add:wf_btree_def find_h_def  entries_list_h.simps norm_find_entry_equal_to_map_lookup)
done


end
