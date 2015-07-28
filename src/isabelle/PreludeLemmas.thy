theory "PreludeLemmas" 

imports 
 	 Main "~~/src/HOL/Library/Code_Target_Numeral"
	 "../../src_ext/lem/isabelle-lib/Lem_pervasives" 
	 "../../src_ext/lem/isabelle-lib/Lem_set_extra" 
	 "../../src_ext/lem/isabelle-lib/Lem_assert_extra" 
	 "gen_isabelle/Btree"
	 "TerminationLemmas"
begin


lemma if_find_indices_returns_index_then_the_element_exists [simp]:
"\<forall> p n ns. find_indices p list = n # ns \<longrightarrow>
       (\<exists> e . (index list n = Some e) \<and> e \<in> set list \<and> (p e = p (list ! n)) \<and> p e \<and>  p (list ! n)) \<and> n < length list "
apply (induct list)
  apply auto
  
  apply (case_tac "p a")
    apply auto
done

lemma find_h_is_correct_helper [simp]:
"\<forall> k env n ns .find_indices (\<lambda>x. k = entry_to_key env x) list = n # ns \<longrightarrow>
       k = entry_to_key env (list ! n)"
apply (induct list)
  apply auto
done

lemma first_returns_something_only_if [simp]:
"\<forall> p i. first xs p = Some i \<longrightarrow> \<not> (xs = []) \<and> \<not>(i = 0) \<and> (i < Suc (length xs))"
apply auto
apply (simp add:first_def)

apply (simp add:first_def)
apply (case_tac "find_indices p xs")
apply auto

apply (simp add:first_def)
apply (case_tac "find_indices p xs")
  apply auto
done

lemma nth_from_1_is_like_nth [simp]:
"\<forall> list n. (nth_from_1 list 0 = None) \<and> (nth_from_1 list (Suc n) = index list n) "
apply (auto simp add:nth_from_1_def)
done

lemma find_trans_of_None_is_None [simp]:
"\<forall> env p s . find_trans env (None,p,s) = (None,p,s)"
apply (simp add:find_trans_def)
done

lemma find_trans_does_not_alter_store:
"\<forall> env a q s b' q' s'. (find_trans env (a,q,s)) = (b',q',s') \<longrightarrow> s = s'"
apply auto
apply (simp add:find_trans_def)
apply auto
apply (case_tac "a")
  (* a = None *)
  apply auto

  (* a = Some aa *)
  apply (case_tac "aa")
    (*aa = Find *)
    apply auto
    apply (case_tac "s q")
      (* s q = None *)
      apply auto

      (* s q = Some a *)
      apply (case_tac a)
        apply auto
        apply (case_tac inode)
        apply auto
        apply (case_tac " nth_from_1 b (case first a (key_lt env key) of None \<Rightarrow> length b | Some i \<Rightarrow> i)")
          apply auto
       
        apply (case_tac lnode)
        apply auto
        apply (case_tac "first list (\<lambda>x. key = entry_to_key env x)")
          apply auto
done

lemma find_trans_result_returns_same_elemen_of_store:
"\<forall> env c p p' s0 s0' r n. 
find_trans env (Some(c),p,s0) = (Some(F_Ret(p',n)),p',s0') \<longrightarrow>
(let page = s0 p in
 let page' = s0' p' in
page = page')
"
apply auto
apply (simp add:find_trans_def)
apply auto
apply (case_tac c)
  (* c = Find *)
  apply auto
  apply (case_tac "s0 p")
    apply auto

    apply (case_tac a)
      apply auto
      apply (case_tac inode)
      apply auto
      apply (case_tac "nth_from_1 b (case first a (key_lt env key) of None \<Rightarrow> length b | Some i \<Rightarrow> i)")
        apply auto

      apply (case_tac lnode)
      apply auto
      apply (case_tac "first list (\<lambda>x. key = entry_to_key env x)")
        apply auto
done        

lemma find_trans_result_returns_f_ret_only_if [simp]:
"\<forall> env c p s0 r n es k. 
find_trans env (Some(c),p,s0) = (Some(F_Ret(p,n)),p,s0) \<longrightarrow>
(case c of
  Find k \<Rightarrow>
( case s0 p of
  Some(LNode(L(es))) \<Rightarrow>
    (case  (first es (\<lambda> x . k = ((entry_to_key   env) x))) of
            Some i => i = n
          | _ => False)
  | _ \<Rightarrow> False)
| _ \<Rightarrow> False)"

apply auto
apply (simp add:find_trans_def)
apply auto
apply (case_tac c)
  (* c = Find *)
  apply auto
  apply (case_tac "s0 p")
    apply auto

    apply (case_tac a)
      apply auto
      apply (case_tac inode)
      apply auto
      apply (case_tac "nth_from_1 b (case first a (key_lt env key) of None \<Rightarrow> length b | Some i \<Rightarrow> i)")
        apply auto

      apply (case_tac lnode)
      apply auto
      apply (case_tac "first list (\<lambda>x. key = entry_to_key env x)")
        apply auto
done

declare norm_find_h.simps [simp del] 

lemma norm_find_h_simps: "
\<forall> env c .
norm_find_h env c (Suc h) = ( (
        (case  c of
          ((Some(F_Ret(p,n)),_,s0)) => (None, s0)
        | (_,_,s0) =>
           (let c' = (find_trans env c) in
           norm_find_h env c' h)
        )))
"
  apply auto
  apply (case_tac h)
    apply (simp add:norm_find_h.simps)
    apply (case_tac a)
      apply auto

      apply (case_tac ab)
        apply auto

    apply (case_tac a)
      apply (simp add:norm_find_h.simps)
    apply auto
    apply (case_tac ab)
      apply auto
      apply (simp_all add:Let_def norm_find_h.simps)
done

lemma find_h_simps:
"
\<forall> env c .
find_h env c (Suc (Suc h)) = ( (
        (case  c of
          ((Some(F_Ret(p,n)),_,s0)) => (None, s0)
        | (_,_,s0) =>
           (let c' = (find_trans env c) in
           norm_find_h env c' h)
        )))
"
apply (simp add:find_h_def norm_find_h_simps Let_def)
done

lemma norm_find_h_simps2:
"\<forall> env k ra s va p i. (find_h env (Some (Find k), ra, s) (Suc (Suc va)) = (Some (p, i), s)) = 
(find_h env (find_trans env (Some (Find k), ra, s)) (Suc va) = (Some (p, i), s))"
apply(simp_all add:find_h_def norm_find_h_simps Let_def)
done

lemma norm_find_h_None_is_None [simp]:
"\<forall> env p s . norm_find_h env (None,p,s) h = (None,s)"
apply (induct h)
  apply (simp add:norm_find_h.simps)

  apply (simp add: norm_find_h_simps)
done

lemma find_h_None_is_None [simp]:
"\<forall> env p s . find_h env (None,p,s) h = (None,s)"
apply (simp add:find_h_def)
apply (case_tac h)
  apply auto
done

lemma norm_find_h_does_not_alter_store:
"\<forall> env c0 p0 s0 opt s1. (norm_find_h env (c0,p0,s0) h = (opt,s1)) \<longrightarrow> (s1=s0)"
apply auto
apply (induct h)
  apply (simp add:norm_find_h.simps find_trans_def)
  apply (case_tac c0)
    (* c0 = None *)
    apply auto

    (* c0 = Some a *)
    apply (case_tac a)
      (* a = Find k *)
      apply (case_tac "s0 p0")
        apply auto

        apply (case_tac aa)
          apply (case_tac inode)
          apply auto
          apply (case_tac "first a (key_lt env key)")
            apply (simp add:nth_from_1_def)
            apply (case_tac b)
              apply auto
              
              apply (case_tac "nth_from_1 b aa")
              apply auto

          apply (case_tac lnode)
          apply auto
          apply (case_tac "first list (\<lambda>x. key = entry_to_key env x)")
            apply auto

      (* a = F_Ret *)
      apply (simp add:norm_find_h_simps find_trans_def)
      apply (case_tac c0)
        apply auto

        apply (case_tac a)
          apply auto
          
          apply (simp add:find_trans_def)
          apply (case_tac "s0 p0")
            apply auto

            apply (case_tac a)
              apply (case_tac inode)
              apply auto
              apply (case_tac "first aa (key_lt env key)")
              apply (simp add:nth_from_1_def)
              apply (case_tac b)
                apply auto
          
                apply (case_tac "nth_from_1 b a")
                apply auto

          apply (case_tac lnode)
          apply auto
          apply (case_tac "first list (\<lambda>x. key = entry_to_key env x)")
            apply auto                
done

lemma find_h_does_not_alter_store:
"\<forall> env c0 p0 s0 opt s1. (find_h env (c0,p0,s0) h = (opt,s1)) \<longrightarrow> (s1=s0)"
apply (simp add:find_h_def)
  apply (case_tac h)
    apply (simp_all add:norm_find_h_does_not_alter_store)
done

lemma find_h_does_not_alter_store_if_wf_btree:
"\<forall> env c0 p0 s0 opt s1.
let n = case s r of Some(LNode(L(es))) \<Rightarrow> (length es) | Some(INode(I(_,es))) \<Rightarrow> (length es) | _ \<Rightarrow> 0 in
 let all_entries = (case (entries_list_h s r h) of (Some list) \<Rightarrow> set list | None \<Rightarrow> {}) in
wf_btree env s (r, all_entries,n) h \<longrightarrow> (find_h env (c0,p0,s0) h = (opt,s1)) \<longrightarrow> (s1=s0)"
apply (simp add:find_h_does_not_alter_store)
done

lemma norm_find_h_always_return_page_id_in_store:
"\<forall> env k r s0 s i p. norm_find_h env ((Some(Find k)),r,s0) h = (Some(p,i),s) \<longrightarrow> (s = s0) \<and> (p \<in> dom s)"
apply (simp add:norm_find_h_does_not_alter_store)
apply auto
apply (induct h)
  apply (simp add:norm_find_h.simps find_trans_def)
  apply (case_tac "s0 r")
      apply auto

      apply (case_tac a)
        apply (case_tac inode)
        apply auto
        apply (case_tac "nth_from_1 b (case first aa (key_lt env k) of None \<Rightarrow> length b | Some i \<Rightarrow> i)")
          apply auto

        apply (case_tac lnode)
        apply auto
        apply (case_tac "first list (\<lambda>x. k = entry_to_key env x)")
          apply auto

  apply (simp add:norm_find_h_simps find_trans_def)
  apply (case_tac "s0 r")
      apply auto

      apply (case_tac a)
        apply (case_tac inode)
        apply auto
        apply (case_tac "nth_from_1 b (case first aa (key_lt env k) of None \<Rightarrow> length b | Some i \<Rightarrow> i)")
          apply auto

        apply (case_tac lnode)
        apply auto
        apply (simp add:norm_find_h.simps)
          apply (case_tac h)
            apply auto
            apply (simp add:find_trans_def)
              apply (case_tac "s0 r")
                apply auto

                apply (case_tac "first list (\<lambda>x. k = entry_to_key env x)")
                  apply auto
                  
        apply (case_tac "first list (\<lambda>x. k = entry_to_key env x)")
          apply auto
done

lemma find_h_always_return_page_id_in_store:
"\<forall> env k r s0 s i p. find_h env ((Some(Find k)),r,s0) h = (Some(p,i),s) \<longrightarrow> (s = s0) \<and> (p \<in> dom s)"
apply (simp add:find_h_def)
apply (case_tac h)
  apply (simp_all add:norm_find_h_always_return_page_id_in_store)
done

lemma norm_find_h_returns_some_only_if:
"\<forall> env c r s p i k. norm_find_h env (c,r,s) h = (Some(p,i),s) \<longrightarrow>
(
  (h = 0 \<and> (find_trans env (c,r,s) = (Some (F_Ret(p,i)),p,s))) 
\<or>
  (h > 0 \<and> (\<exists> c'. c' = find_trans env (c,r,s) \<and> norm_find_h env c' (h-(1::nat)) = (Some(p,i),s)) )
)
"
apply (case_tac h)
  apply auto
  apply (simp add:norm_find_h.simps find_trans_def)
  apply (case_tac c)
    apply auto

    apply (case_tac a)
      apply auto
      apply (case_tac "s r")
        apply auto

        apply (case_tac a)
          apply (case_tac inode)
          apply auto
          apply (case_tac "first aa (key_lt env key)")
            apply (case_tac b)
              apply auto

              apply (case_tac "nth_from_1 b a")
              apply auto

         apply (case_tac lnode)
          apply (case_tac "first list (\<lambda>x. key = entry_to_key env x)")
            apply auto

  apply (simp add:norm_find_h_simps find_trans_def)
  apply (case_tac c)
    apply auto

    apply (case_tac a)
      apply auto
      apply (case_tac "s r")
        apply (simp_all add:find_trans_def)
done



declare norm_entries_list_h.simps [simp del]
lemma norm_entries_list_h_simps:
"\<forall> s0 r. norm_entries_list_h s0 r (Suc h) =
(case   s0 r of
          Some node \<Rightarrow> (
          (case  node of
            LNode _ => None
          | INode(I(_,qs)) => (
            (let list_of_lists_of_entries = (List.map (\<lambda> q .  norm_entries_list_h s0 q h) qs) in
            if ((\<forall> x \<in> (set list_of_lists_of_entries).  \<not> (x = None))) then
              Some(List.concat (List.map the list_of_lists_of_entries))
            else
              None)
          )))
          | _ \<Rightarrow> None)
"
apply auto
apply (simp add:norm_entries_list_h.simps)
apply (case_tac "s0 r")
  apply auto

  apply (case_tac a)
    apply (case_tac inode)
    apply auto
done

lemma norm_entries_list_returns_None_if [simp]:
"\<forall> ds qs s r. norm_entries_list_h s r h = None \<longrightarrow>
(s r = None)
\<or>
(h = 0 \<and> (case s r of Some(LNode(_)) \<Rightarrow> False | _ \<Rightarrow> True))
\<or>
((h > 0) \<and> (case s r of Some(INode(I(_,qs))) \<Rightarrow> (\<exists> q \<in> set qs. (norm_entries_list_h s q (h-(1::nat)) = None)) | _ \<Rightarrow> True))
"
apply (case_tac h)
  apply (simp add:norm_entries_list_h.simps)
  apply auto
  apply (case_tac "s r")
    apply auto

    apply (case_tac a)
      apply auto
      apply (case_tac lnode)
      apply auto

  apply (case_tac "s r")
    apply auto

    apply (case_tac a)
      apply (case_tac inode)
      apply auto

      apply (simp add:norm_entries_list_h_simps)
done

lemma map_and_first_are_equal:
"\<forall> k env.
map_of (map (\<lambda>e. (entry_to_key env e, e)) list) k =
(case first list (\<lambda>x. k = entry_to_key env x) of None \<Rightarrow> None | Some i \<Rightarrow> nth_from_1 list i)"
apply auto
apply (induct list)
  (* list = [] *)
  apply (simp add:first_def)

  (* list = a#list *)
  apply (simp add:first_def)
  apply auto
  
    apply (case_tac "map Suc (find_indices (\<lambda>x. k = entry_to_key env x) list)")
      apply auto
done

lemma nth_first_is_list_find_simp:
"\<forall> p. List.find p list = nth_from_1 list (case first list p of None \<Rightarrow> 0 | Some i \<Rightarrow> i) "
apply (induct list)
  apply (simp add:nth_from_1_def first_def)

  apply auto
  apply (simp add:first_def)

  apply (simp add:first_def)
  apply (case_tac "find_indices p list ")
    apply auto
done

lemma map_and_listfind_equal:
"\<forall> k env.
map_of (map (\<lambda>e. (entry_to_key env e, e)) list) k = List.find (\<lambda> x . k = entry_to_key env x) list"
apply auto
apply (induct list)
  apply auto
done

lemma listfind_append [simp] :
"\<forall> P. List.find P (list @ list') = (let res = List.find P list in if res = None then List.find P list' else res)"
apply auto
apply (case_tac "List.find P list")
  apply auto
  apply (induct list)
    apply auto

  apply (induct list)
    apply auto
done

lemma listfind_append_list_with_concat :
"\<forall> k P e list. None = List.find P list \<longrightarrow> List.find P (List.concat list') = List.find P ((List.concat list') @ list)"
apply auto
apply (case_tac " List.find P (List.concat list')")
  apply auto
done

lemma listfind_and_concat1:
"\<forall> P e list. Some e = List.find P list \<longrightarrow> \<not> None = List.find P ((List.concat list') @ list)"
apply auto
  apply (case_tac "List.find P (List.concat list')")
      apply auto
done

lemma listfind_concat_a_list_exists [simp]:
"\<forall> P e. Some e = List.find P (List.concat list) \<longrightarrow> (\<exists> list' \<in> set list . Some e  = List.find P list' )"
apply auto
apply (induct list)
  apply auto

  apply (case_tac "List.find P a")
    apply auto
done

lemma nth_from_1_length [simp]: "nth_from_1 b (length b) = None \<Longrightarrow> b=[]"
apply (case_tac b)
  apply auto
done

lemma sorry_fixme: "P"
  sorry

lemma listfind_returns_the_first_element_satisfying_P [simp]: 
"(List.find P xs = None) \<Longrightarrow> List.find P y \<noteq> None \<Longrightarrow> List.find P y = List.find P (List.concat (xs#(y#ys)))"
apply simp
apply (case_tac "List.find P y")
 apply simp_all
done

lemma listfind_returns_the_first_element_satisfying_P2 [simp]: 
"(List.find P xs = None) \<Longrightarrow> P y \<Longrightarrow> List.find P (y#ys) = (index (xs@(y#ys)) (length xs))"
apply auto
done


lemma norm_wf_btree_h0_is_true_if:
"\<forall> env s r all_entries n. 
norm_wf_btree env s (r, all_entries,n) 0 \<longrightarrow>
(case s r of 
  Some(LNode (L es)) \<Rightarrow>
    (n = length es)
    \<and>
    (n \<le> maxN env)
    \<and>
    (set es =  all_entries)
    \<and>
    (sorted_by (entry_lt env) es)
  | _ \<Rightarrow> False)
"
apply auto
apply (case_tac "s r")
 apply simp

 apply (case_tac a)
 apply simp

 apply (case_tac lnode)
 apply (simp add:Let_def)
 apply (case_tac "length list = n \<and> length list \<le> maxN env")
  apply simp
  apply (case_tac "all_entries = set list")
   apply simp_all
done

lemma norm_wf_btree_requires_qs_length_to_be_at_least_2_if_inode_exist:
"\<forall> env k c s r ds qs. 
s r = Some(INode(I(ds,qs))) \<longrightarrow>
(let n = case s r of Some(LNode(L(es))) \<Rightarrow> (length es) | Some(INode(I(_,es))) \<Rightarrow> (length es) | _ \<Rightarrow> 0 in
 let all_entries = (case (entries_list_h s r h) of (Some list) \<Rightarrow> set list | None \<Rightarrow> {}) in
norm_wf_btree env s (r, all_entries,n) h \<longrightarrow> (Suc(length ds) = length qs) \<and> (length ds > 0) \<and> (length qs \<ge> 2))"
apply (induct h)
  apply simp
  
  apply auto
  apply (case_tac "Suc (length ds) = length qs")
    apply auto

apply (case_tac ds)
  apply auto
done

lemma ordered_norm_entries_list_if_norm_wf_btree:
"norm_wf_btree env s (r,ss,n) h \<longrightarrow> 
sorted_by (entry_lt env) (case (norm_entries_list_h s r h) of Some list \<Rightarrow> list | _ \<Rightarrow> [])"
apply (case_tac h)
 apply simp
 apply (case_tac "s r")
  apply simp

  apply (case_tac a)
   apply simp

   apply (case_tac lnode)
   apply (simp add:Let_def)
   apply (case_tac "length list \<noteq> n")
    (*length list \<noteq> n*)
    apply simp

    (* length list = n*)
    apply (case_tac "length list > maxN env")
     apply simp

     (*length list \<le> maxN env*)
     apply simp
     apply (case_tac "ss \<noteq> set list")
      apply simp

      (* ss = set list *)
      apply (simp add:norm_entries_list_h.simps)
 (* Suc nat*)
 apply simp
 apply (case_tac "s r")
  apply simp

  apply (case_tac a)
   defer
   (* a = lnode *)
   apply simp

   apply (case_tac inode)
   apply (case_tac prod)
   apply (simp add:Let_def)
   apply (case_tac "length b \<noteq> n")
    (*length list \<noteq> n*)
    apply simp

    (* length list = n*)
    apply (case_tac "length b \<noteq> Suc (length aa)")
     apply simp

     (*length list \<le> maxN env*)
     apply simp
     apply (case_tac aa)
      apply simp

      (*aa = ab # list *)
      apply (simp add:Let_def)
      apply (case_tac "norm_entries_list_h s r (Suc nat)")
       apply simp

       (* norm_entries_list_h s r (Suc nat) = Some ac*)
       apply simp 
       apply (case_tac "ss \<noteq> set ac")
        apply simp

        (* ss = set ac*)
        apply simp
        apply (case_tac "norm_entries_list_h s (b ! Suc (length list)) nat")
         apply simp

         (* norm_entries_list_h s (b ! Suc (length list)) nat = Some ad*)
         apply simp
         apply (case_tac "\<not>(\<forall>s\<in>set ad. key_lte env ((ab # list) ! length list) (entry_to_key env s))")
          apply simp
          apply force

          (*(\<forall>s\<in>set ad. key_lte env ((ab # list) ! length list) (entry_to_key env s)) = True*)
          apply simp
          apply (case_tac "norm_entries_list_h s (b ! 0) nat")
           apply simp

           (*norm_entries_list_h s (b ! 0) nat = ab*)
           apply simp
           apply (case_tac "\<not>(\<forall>s\<in>set ae. key_lt env (entry_to_key env s) ab)")
            apply simp
            apply force

            (* \<forall>s\<in>set ae. key_lt env (entry_to_key env s) ab *)
            apply simp
            
oops

end
