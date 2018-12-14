
import data.vector

variables {n : ℕ} {α : Type}

inductive column
| left : column
| middle : column
| right : column

-- TODO: apparently arrays could be very natural in this situation

-- okay so we encode valid states as fixed length sequences
def validstate (n : ℕ) := vector column n

lemma update_preserve_length {a : α} (l : list α) : 
    ∀ i, list.length l = list.length (list.update_nth l i a) :=
begin
    induction l; intro i; cases i; simp [list.update_nth, list.length]; rw l_ih i
end

def update_nth : vector α n → fin n → α → vector α n
| v i a := ⟨ list.update_nth v.val i.val a, by { rw ←(update_preserve_length v.val), exact v.property } ⟩ 

def zero_fin (n : ℕ) : fin (nat.succ n) := ⟨0, dec_trivial⟩

lemma update_nth_helper (v : vector α n) (i : fin n) (a b : α)
    : vector.cons b (update_nth v i a) = update_nth (vector.cons b v) (fin.succ i) a :=
begin
    cases v,
    simp [update_nth, *],
    cases i,
    rw fin.succ,
    simp [vector.cons],
    refl -- hell yeah boiiii
end

lemma vector_nth_helper (v : vector α n) (i : fin n) (a : α)
    : vector.nth (vector.cons a v) (fin.succ i) = vector.nth v i :=
begin
    induction n,
    {
        cases i,
        cases i_is_lt
    },
    {
        cases i,
        cases v,
        simp [fin.succ, vector.cons, vector.nth],
        refl
    } -- awww yiss
end

def movestone (s : validstate n) (i : fin n) (dest : column)
    (valid_move: ∀j, j > i → vector.nth s j ≠ dest ∧ vector.nth s j ≠ vector.nth s i) : validstate n :=
update_nth s i dest

/-- `refl_trans r`: relexive and transitive closure of `r` -/
inductive refl_trans {α : Sort*} (r : α → α → Prop) (a : α) : α → Prop
| refl {} : refl_trans a
| tail {b c} : refl_trans b → r b c → refl_trans c

def one_step : validstate n → validstate n → Prop
| s1 s2 := ∃ (i : fin n) (dest : column) pf, s2 = movestone s1 i dest pf

def multi_step : validstate n → validstate n → Prop := refl_trans one_step

lemma vector.eq_iff {n} {a b : vector α n} : a = b ↔ a.1 = b.1 :=
begin
  cases a; cases b,
  split,
  { intro h, exact congr_arg subtype.val h },
  { apply vector.eq }
end

lemma update_with_self (l : list α) (i : ℕ) (h : i < list.length l) :
    l = list.update_nth l i (list.nth_le l i h) :=
begin
    induction l generalizing i,
    {
        cases h,
    },
    {
        cases i,
        {
            simp [list.update_nth],
        },
        {
            simp [list.update_nth],
            apply l_ih,
        }
    }
end

lemma conseq_updates (l : list α) (a b : α) (i : ℕ) :
    list.update_nth (list.update_nth l i a) i b = list.update_nth l i b :=
begin
    induction l generalizing i,
    {
        refl,
    },
    {
        cases i,
        {
            refl,
        },
        {
            simp [list.update_nth],
            apply l_ih
        }
    }
end

lemma update_reversibility (i : fin n) (a : column) (s1 s2 : validstate n) (h : s1 = update_nth s2 i a) :
  s2 = update_nth s1 i (vector.nth s2 i) :=
begin
    apply vector.eq,
    change s2.val = list.update_nth s1.val (i.val) (vector.nth s2 i),
    cases s2,
    cases s1,
    cases i,
    simp [vector.nth],
    rw ←s2_property at i_is_lt,
    rw update_nth at h,
    have yolo := (iff.elim_left vector.eq_iff) h,
    simp at yolo,
    induction s1_val generalizing i_val s2_val n,
    {
        rw ← s1_property at i_is_lt,
        cases i_is_lt,
    },
    {
        rw yolo,
        rw conseq_updates,
        exact update_with_self _ _ _
    }
end

lemma fin_pred (j : fin (nat.succ n)) (k : fin n) (h : j > fin.succ k)
    : ∃ (i : fin n), fin.succ i = j ∧ i > k :=
begin
    cases j,
    cases j_val,
    {
        cases h,        
    },
    {
        cases k,
        exact ⟨ ⟨ j_val, nat.lt_of_succ_lt_succ j_is_lt ⟩, ⟨ rfl, nat.lt_of_succ_lt_succ h ⟩ ⟩
    }
end

lemma jth_after_update_i (i j : fin n) (a : column) (s : validstate n) (h : i < j)
    : vector.nth (update_nth s i a) j = vector.nth s j :=
begin
    cases s,
    induction s_val generalizing n i j,
    {
        simp at s_property,
        cases i,
        rw ←s_property at i_is_lt,
        cases i_is_lt,
    },
    {
        cases n,
        {
            cases i,
            cases i_is_lt,
        },
        {
            have yolo : list.length s_val_tl = n := begin
                    simp [nat.succ_eq_add_one] at s_property,
                    rw nat.add_comm at s_property,
                    exact nat.add_right_cancel s_property
            end,
            cases i,
            cases i_val,
            sorry
        }
    }
end

lemma ith_after_update_i (i : fin n) (a : column) (s : validstate n)
    : vector.nth (update_nth s i a) i = a :=
begin
    cases i,
    cases s,
    induction s_val generalizing n i_val,
    {
        rw ←s_property at i_is_lt,
        cases i_is_lt,
    },
    {
        cases n,
        {
            cases i_is_lt,
        },
        {
            cases i_val,
            {
                simp *,
                refl,
            },
            {
                simp [vector.nth, update_nth, list.update_nth, *],
                apply s_val_ih,
                {
                    exact nat.lt_of_succ_lt_succ i_is_lt,
                },
                {
                    simp [nat.succ_eq_add_one] at s_property,
                    rw nat.add_comm at s_property,
                    exact nat.add_right_cancel s_property
                }
            }
        }
    }
end

lemma one_step_symm {s1 s2 : validstate n} (h: one_step s1 s2) : one_step s2 s1 :=
begin
    cases h,
    cases h_h,
    cases h_h_h,
    cases n,
    {
        cases h_w,
        cases h_w_is_lt,
    },
    rw movestone at h_h_h_h,
    rw one_step,
    apply exists.intro h_w,
    apply exists.intro (vector.nth s1 h_w),
    apply exists.intro,
    {
        exact update_reversibility _ _ _ _ h_h_h_h,
    },
    {
        intros j hj,
        rw [h_h_h_h, jth_after_update_i _ _ _ _ hj, ith_after_update_i],
        exact and.swap (h_h_h_w j hj)
    }
end

lemma multi_step_transitive {a b c : validstate n} (hab : multi_step a b) (hbc : multi_step b c) : multi_step a c :=
begin
  induction hbc,
  case refl_trans.refl { assumption },
  case refl_trans.tail : c d hbc hcd hac { exact hac.tail hcd }
end

lemma multi_step_symmetric {a b : validstate n} (hab : multi_step a b) : multi_step b a :=
begin
    induction hab,
    {
        exact refl_trans.refl
    },
    case refl_trans.tail : c d hbc hcd hac {
        exact multi_step_transitive (refl_trans.tail refl_trans.refl (one_step_symm hcd)) hac
    }
end

-- picks an unused column
def third_column : column → column → column
| column.left column.right := column.middle
| column.right column.left := column.middle
| column.left _ := column.right
| column.right _ := column.left
| column.middle column.left := column.right
| column.middle _ := column.left

lemma third_column_unused : ∀ c1 c2, third_column c1 c2 ≠ c1 ∧ third_column c1 c2 ≠ c2 :=
begin
    intros c1 c2,
    cases c1;
    cases c2;
    {
        apply and.intro,
        repeat { simp [third_column] }
    }
end

lemma equiv_cons (s1 s2 : validstate n) (a : column) (h : multi_step s1 s2)
    : multi_step (vector.cons a s1) (vector.cons a s2) :=
begin
    induction h,
    {
        exact refl_trans.refl
    },
    {
        apply refl_trans.tail h_ih,
        cases h_a_1,
        cases h_a_1_h,
        cases h_a_1_h_h,
        rw one_step,
        apply exists.intro (fin.succ h_a_1_w),
        apply exists.intro h_a_1_h_w,
        apply exists.intro _,
        {
            rw [movestone, h_a_1_h_h_h, movestone],
            apply update_nth_helper
        },
        {
            -- repackage IH pf
            intros j h2,
            rw vector_nth_helper,
            have yolo := fin_pred j h_a_1_w h2,
            cases yolo,
            rw ←yolo_h.left,
            rw vector_nth_helper,
            exact (h_a_1_h_h_w yolo_w yolo_h.right)
        }
    }
end

lemma nth_of_list_repeat (a : α) (i n : ℕ) (h : i < list.length (list.repeat a n))
    : list.nth_le (list.repeat a n) i h = a :=
begin
    induction i generalizing n;
    {
        cases n,
        {
            cases h,
        },
        {
            simp *,
        }
    }
end

lemma nth_of_repeat (i : fin n) (a : α)
    : vector.nth (vector.repeat a n) i = a :=
begin
    cases n,
    {
        cases i,
        cases i_is_lt,
    },
    {
        cases i,
        induction i_val,
        {
            refl,
        },
        {
            simp [vector.repeat, vector.nth],
            have i_lt_n := nat.lt_of_succ_lt_succ i_is_lt,
            have len_repeat_n : ∀ k, list.length (list.repeat a k) = k := begin
                intro k,
                induction k;
                simp *,
            end,
            rw ←(len_repeat_n n) at i_lt_n,
            exact nth_of_list_repeat a i_val_n n i_lt_n,
        }
    }    
end

-- TODO: can we do without the lt arg?
lemma zeroth_of_cons (a : α) (v : vector α n) (lt : 0 < nat.succ n)
    : vector.nth (vector.cons a v) ⟨0, lt⟩ = a :=
begin
        cases v,
        simp [vector.cons, vector.nth, *],
end

lemma all_states_equiv (s1 s2 : validstate n) : multi_step s1 s2 :=
begin
    induction n,
    {   
        have s1_eq_s2 : s1 = s2 := begin
            cases s1,
            cases s2,
            cases s1_val,
            {
                cases s2_val,
                {
                    refl,
                },
                {
                    cases s2_property,
                }
            },
            {
                cases s1_property,
            }
        end,
        rw s1_eq_s2,
        exact refl_trans.refl,
    },
    {
        -- IDEA:
        -- s1 : [x0, x1, ..., x(n-1)],
        -- s2 : [y0, y1, ..., y(n-1)],
        -- let z = third_column x0 y0
        -- by induction hypothesis:
        -- [x1, ..., x(n-1)] ~ [z, ..., z]
        -- [y1, ..., y(n-1)] ~ [z, ..., z]
        -- then by prefix lemma,
        -- s1 ~ [x0, z, ..., z]
        -- s2 ~ [y0, z, ..., z]
        -- and we can go from [x0, z, ..., z] to [y0, z, ..., z] in one step
        -- since ~ (multi_step) is an equivalence (trans, symm), s1 ~ s2
        cases s1,
        cases s1_val,
        {
            -- not possible
            cases s1_property,
        },
        cases s2,
        cases s2_val,
        {
            -- not possible
            cases s2_property,
        },
        -- z = third_column s1_val_hd s2_val_hd

        -- s1 ~ [x0, z, ..., z]
        have proppp1 : list.length s1_val_tl = n_n := begin
            cases s1_property,
            refl
        end,
        -- FIXME: this is a mess lol
        have s1_equiv_s10zzz : multi_step ⟨s1_val_hd :: s1_val_tl, s1_property⟩ (vector.cons s1_val_hd (vector.repeat (third_column s1_val_hd s2_val_hd) n_n)) :=
            begin
                have yolo : (vector.cons s1_val_hd ⟨s1_val_tl, proppp1⟩) = ⟨s1_val_hd :: s1_val_tl, s1_property⟩ := rfl,
                rw ←yolo,
                apply equiv_cons,
                apply n_ih,
            end,

        -- s2 ~ [y0, z, ..., z]
        have proppp2 : list.length s2_val_tl = n_n := begin
            cases s2_property,
            refl
        end,
        have s2_equiv_s20zzz : multi_step ⟨s2_val_hd :: s2_val_tl, s2_property⟩ (vector.cons s2_val_hd (vector.repeat (third_column s1_val_hd s2_val_hd) n_n)) :=
            begin
                have yolo : (vector.cons s2_val_hd ⟨s2_val_tl, proppp2⟩) = ⟨s2_val_hd :: s2_val_tl, s2_property⟩ := rfl,
                rw ←yolo,
                apply equiv_cons,
                apply n_ih,
            end,

        have small_step : one_step (vector.cons s1_val_hd (vector.repeat (third_column s1_val_hd s2_val_hd) n_n))
            (vector.cons s2_val_hd (vector.repeat (third_column s1_val_hd s2_val_hd) n_n)) :=
        begin
            rw one_step,

            apply exists.intro (zero_fin n_n),
            {
                apply exists.intro s2_val_hd,
                apply exists.intro,
                {
                    rw movestone,
                    refl,
                },
                {
                    intros j h,
                    rw zero_fin at h,
                    cases j,
                    cases j_val,
                    {
                        cases h, -- j_val of type succ
                    },
                    apply and.intro,
                    {
                        rw ←fin.succ,
                        {
                            rw [vector_nth_helper, nth_of_repeat],
                            exact (third_column_unused s1_val_hd s2_val_hd).right
                        },
                        {
                            exact nat.lt_of_succ_lt_succ j_is_lt
                        }
                    },
                    {
                        rw ←fin.succ,
                        {
                            rw [vector_nth_helper, zero_fin, nth_of_repeat, zeroth_of_cons],
                            exact (third_column_unused _ _).left
                        },
                        {
                            exact nat.lt_of_succ_lt_succ j_is_lt
                        }
                    }
                }
            }
        end,
        
        exact multi_step_transitive (refl_trans.tail s1_equiv_s10zzz small_step) (multi_step_symmetric s2_equiv_s20zzz)
    }
end


theorem towers_hanoi_solvable : ∀ n : ℕ, multi_step (vector.repeat column.left n) (vector.repeat column.right n) :=
    λ n, all_states_equiv (vector.repeat column.left n) (vector.repeat column.right n)
