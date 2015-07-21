theory "PreludeLemmas" 

imports 
 	 Main "~~/src/HOL/Library/Code_Target_Numeral"
	 "../../src_ext/lem/isabelle-lib/Lem_pervasives" 
	 "../../src_ext/lem/isabelle-lib/Lem_set_extra" 
	 "../../src_ext/lem/isabelle-lib/Lem_assert_extra" 
	 "gen_isabelle/Btree"

begin

termination norm_wf_btree by lexicographic_order
termination norm_find_h by lexicographic_order
termination from_to_h by lexicographic_order
termination norm_entries_list_h by lexicographic_order

lemma btree_height_0_is_not_wf: " ((\<forall> e. \<forall> s. \<forall> c.  wf_btree e s c(( 0 :: nat)) \<longleftrightarrow> False))"
apply (simp add:wf_btree_def)
done

lemma wf_btree_requires_qs_length_to_be_at_least_2_if_inodes_exist [simp]:
"\<forall> env k c s r ds qs. 
s r = Some(INode(I(ds,qs))) \<longrightarrow>
(let n = case s r of Some(LNode(L(es))) \<Rightarrow> (length es) | Some(INode(I(_,es))) \<Rightarrow> (length es) | _ \<Rightarrow> 0 in
 let all_entries = (case (entries_list_h s r h) of (Some list) \<Rightarrow> set list | None \<Rightarrow> {}) in
wf_btree env s (r, all_entries,n) h \<longrightarrow> (Suc(length ds) = length qs) \<and> (length ds > 0) \<and> (length qs \<ge> 2))"
apply (simp add:wf_btree_def)
apply (induct h rule:norm_wf_btree.induct)
  apply simp
  
  apply auto
  apply (case_tac "Suc (length ds) = length qs")
    apply auto

apply (case_tac ds)
  apply auto
oops

lemma if_find_indices_finds_index_then_the_element_exists [simp]:
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

lemma find_trans_does_not_alter_store [simp]:
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

lemma find_trans_result_returns_same_elemen_of_store [simp]:
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

lemma norm_find_h_does_not_alter_store [simp]:
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

lemma find_h_does_not_alter_store [simp]:
"\<forall> env c0 p0 s0 opt s1. (find_h env (c0,p0,s0) h = (opt,s1)) \<longrightarrow> (s1=s0)"
apply (simp add:find_h_def)
  apply (case_tac h)
    apply auto
done

lemma find_h_does_not_alter_store_if_wf_btree [simp]:
"\<forall> env c0 p0 s0 opt s1.
let n = case s r of Some(LNode(L(es))) \<Rightarrow> (length es) | Some(INode(I(_,es))) \<Rightarrow> (length es) | _ \<Rightarrow> 0 in
 let all_entries = (case (entries_list_h s r h) of (Some list) \<Rightarrow> set list | None \<Rightarrow> {}) in
wf_btree env s (r, all_entries,n) h \<longrightarrow> (find_h env (c0,p0,s0) h = (opt,s1)) \<longrightarrow> (s1=s0)"
apply auto
done

lemma norm_find_h_always_return_page_id_in_store [simp]:
"\<forall> env k r s0 s i p. norm_find_h env ((Some(Find k)),r,s0) h = (Some(p,i),s) \<longrightarrow> (s = s0) \<and> (p \<in> dom s)"
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

lemma find_h_always_return_page_id_in_store [simp]:
"\<forall> env k r s0 s i p. find_h env ((Some(Find k)),r,s0) h = (Some(p,i),s) \<longrightarrow> (s = s0) \<and> (p \<in> dom s)"
apply (simp add:find_h_def)
apply (case_tac h)
  apply auto
done

lemma norm_find_h_returns_some_only_if [simp]:
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

lemma norm_find_h_is_correct [simp]:
"\<forall> env s r n k p i es. norm_find_h env ((Some(Find k)),r,s) h = (Some(p,i),s) \<longrightarrow> (p \<in> dom s) 
\<and> (case (s p) of (Some(LNode(L(es)))) \<Rightarrow> (case (nth_from_1 es i) of Some e \<Rightarrow> (e \<in> set es) \<and> (k = (entry_to_key env e)) | _ \<Rightarrow> False) | _ \<Rightarrow> False)"
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

lemma listfind_concat_a_list_exists1 [simp]:
"\<forall> P e. Some e = List.find P (List.concat list) \<longrightarrow> (\<exists> list' \<in> set list . Some e  = List.find P list' \<longrightarrow>
List.find P (List.concat list) = List.find P list')"
apply auto
apply (case_tac list)
  apply auto
done

lemma norm_find_entry_equal_to_map_lookup1 [simp]:
"\<forall> env k c s r .
let all_entries = (case (norm_entries_list_h s r h) of (Some list) \<Rightarrow> list | None \<Rightarrow> []) in
find_entry (norm_find_h env (Some(Find k),r,s) h) = 
(map_of (map (\<lambda> e . (entry_to_key env e,e)) all_entries) k)"
apply (simp add:map_and_listfind_equal)
apply auto
apply (induct h)
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

  apply (simp add:norm_find_h_simps find_trans_def)
  apply (case_tac "s r")
    apply (simp add:find_entry.simps norm_entries_list_h_simps)

    apply (case_tac a)
      apply (case_tac inode)
      apply auto
      apply (case_tac "first aa (key_lt env k)")
      apply auto
        apply (case_tac b)
          apply (simp add:find_entry.simps norm_entries_list_h_simps)

          apply (simp add: norm_entries_list_h_simps)
          apply auto
          (* it is necessary to show that find does not need to enter all the branches *)
            apply (case_tac "List.find (\<lambda>x. k = entry_to_key env x) y")
              apply auto
              apply (case_tac "norm_entries_list_h s ((a # list) ! length list) h")
                apply auto


oops

lemma norm_find_entry_equal_to_map_lookup [simp]:
"\<forall> env k c s r .
let all_entries = (case (norm_entries_list_h s r h) of (Some list) \<Rightarrow> list | None \<Rightarrow> []) in
find_entry (norm_find_h env (Some(Find k),r,s) h) = 
(map_of (map (\<lambda> e . (entry_to_key env e,e)) all_entries) k)"
apply (simp add:Let_def map_and_first_are_equal)
apply (induct h)
  apply auto
  apply (simp add:norm_find_h.simps find_trans_def)
  apply (case_tac "s r")
    apply (simp add:find_entry.simps)
    apply (simp add:norm_entries_list_h.simps first_def)
    
    apply (case_tac a)
      apply (case_tac inode)
        apply auto
        apply (case_tac "first aa (key_lt env k)")
          apply auto
          apply (case_tac b)
            apply (simp add:find_entry.simps)
            apply (simp add:norm_entries_list_h.simps first_def)
            
            apply (case_tac "nth_from_1 b (length b)")
              apply auto

              apply (simp add:find_entry.simps)
              apply (simp add:norm_entries_list_h.simps first_def)
            
            apply (case_tac "nth_from_1 b a")
              apply (simp add:find_entry.simps)
              apply (simp add:norm_entries_list_h.simps first_def)

              apply auto
              apply (simp add:find_entry.simps)
              apply (simp add:norm_entries_list_h.simps first_def)


      apply (case_tac lnode)
      apply auto
      apply (case_tac "first list (\<lambda>x. k = entry_to_key env x)")
        apply (simp add:find_entry.simps)
        apply (simp add:norm_entries_list_h.simps)

        apply (simp add:find_entry.simps)
        apply (simp add:norm_entries_list_h.simps)

  apply (simp add:norm_find_h_simps find_trans_def)
  apply (case_tac "s r")
    apply (simp add:find_entry.simps)
    apply (simp add:norm_entries_list_h.simps first_def)
    
    apply (case_tac a)
      apply (case_tac inode)
      apply auto
      apply (case_tac "first aa (key_lt env k)")
        apply auto
        apply (case_tac b)
          apply (simp add:find_entry.simps)

          apply (simp add:norm_entries_list_h_simps first_def)
          apply (simp add:norm_entries_list_h_simps)
          apply auto
          
    
(* THIS IS THE LNODE CASE, uncomment after INODE CASE is solved
      apply (case_tac lnode)
      apply auto
      apply (case_tac "first list (\<lambda>x. k = entry_to_key env x)")
        apply (simp add:find_entry.simps)
        apply (simp add:norm_entries_list_h_simps first_def)

        apply (case_tac nat)
          apply (simp add:norm_find_h.simps find_trans_def find_entry.simps)
          apply (simp add:norm_entries_list_h.simps first_def)

          apply (simp add:norm_find_h_simps find_trans_def find_entry.simps)
          apply (simp add:norm_entries_list_h.simps first_def)
*)          
oops
end
