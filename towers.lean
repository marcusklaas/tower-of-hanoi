
import data.vector

inductive column
| left : column
| middle : column
| right : column

-- TODO: apparently arrays could be very natural in this situation

-- okay so we encode valid states as fixed length sequences
def validstate (n : ℕ) := vector column n

#check lt_irrefl
#check linear_order
#check well_founded
#check nat.add_one_ne_zero

lemma update_preserve_length {α : Type} {a : α} (l : list α) : 
    ∀ i, list.length l = list.length (list.update_nth l i a) :=
begin
    induction l; intro i; cases i; simp [list.update_nth, list.length]; rw l_ih i
end

def update_nth {n : ℕ} {α : Type} : vector α n → fin n → α → vector α n
| ⟨l, h⟩ i a := ⟨ list.update_nth l i.val a, by { rw ←(update_preserve_length l), exact h } ⟩ 

lemma update_nth_helper {n : ℕ} {α : Type} (v : vector α n) (i : fin n) (a b : α)
    : vector.cons b (update_nth v i a) = update_nth (vector.cons b v) (fin.succ i) a :=
begin
    cases v,
    simp [update_nth, *],
    cases i,
    rw fin.succ,
    simp [vector.cons],
    rw update_nth,
    refl -- hell yeah boiiii
end

-- TODO: make α and n variables?
lemma list_update_nth_idempotent {α : Type} (l : list α) (i : ℕ) (a : α)
    : list.update_nth l i a = list.update_nth (list.update_nth l i a) i a :=
begin
    induction l generalizing i, -- awwww yisss, generalizing ftw
    {
        refl
    },
    {
        cases i,
        {
            refl,
        },
        {
            simp [list.update_nth, *],
            exact l_ih i
        }
    }
end

-- FIXME: these lemmas are likely useless lol
lemma update_nth_idempotent {α : Type} {n : ℕ} (v : vector α n) (i : fin n) (a : α)
    : update_nth v i a = update_nth (update_nth v i a) i a :=
begin
    cases v,
    repeat { rw [update_nth] } ,
    cases i,
    simp *,
    have yolo := list_update_nth_idempotent v_val i_val a,
    sorry -- ARGH, feels like we're close!
end

lemma vector_nth_helper {n : ℕ} {α : Type} (v : vector α n) (i : fin n) (a : α)
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

def movestone {n : ℕ} (s : validstate n) (i : fin n) (dest : column)
    (valid_move: ∀j, j > i → vector.nth s j ≠ dest ∧ vector.nth s j ≠ vector.nth s i) : validstate n :=
update_nth s i dest

/-- `refl_trans r`: relexive and transitive closure of `r` -/
inductive refl_trans {α : Sort*} (r : α → α → Prop) (a : α) : α → Prop
| refl {} : refl_trans a
| tail {b c} : refl_trans b → r b c → refl_trans c

def one_step {n : ℕ} : validstate n → validstate n → Prop
| s1 s2 := ∃ (i : fin n) (dest : column) pf, s2 = movestone s1 i dest pf

def multi_step {n : ℕ} : validstate n → validstate n → Prop := refl_trans one_step

lemma one_step_symm {n : ℕ} {s1 s2 : validstate n} (h: one_step s1 s2) : one_step s2 s1 :=
begin
    cases h,
    cases h_h,
    cases h_h_h,
    simp [movestone, update_nth] at h_h_h_h,
    rw one_step,
    apply exists.intro h_w,
    apply exists.intro h_h_w,
    apply exists.intro,
    {
        rw movestone,
        -- rw h_h_h_h,
        -- rw ←update_nth_idempotent,
        sorry
    },
    {
        intros j hj,
        specialize h_h_h_w j hj,
        cases h_h_h_w,
        apply and.intro,
        {
            sorry
        },
        {
            sorry
        }
    }
end

lemma multi_step_transitive {n : ℕ} {a b c : validstate n} (hab : multi_step a b) (hbc : multi_step b c) : multi_step a c :=
begin
  induction hbc,
  case refl_trans.refl { assumption },
  case refl_trans.tail : c d hbc hcd hac { exact hac.tail hcd }
end

lemma multi_step_symmetric {n : ℕ} {a b : validstate n} (hab : multi_step a b) : multi_step b a :=
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

def zero_fin (n : ℕ) : fin (nat.succ n) := ⟨0, dec_trivial⟩

lemma equiv_cons {n : ℕ} (s1 s2 : validstate n) (a : column) (h : multi_step s1 s2)
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
            intro j,
            intro h2,
            --specialize h_a_1_h_h_w j,
            apply and.intro,
            {
                have yolo := vector_nth_helper h_b h_a_1_w a,

                sorry
            },
            {
                rw vector_nth_helper,
                sorry
            }
        }
    }
end

#check list.repeat

lemma nth_of_list_repeat {α : Type} (a : α) (i n : ℕ) (h : i < list.length (list.repeat a n))
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

lemma nth_of_repeat {α : Type} {n : ℕ} (i : fin n) (a : α)
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
lemma zeroth_of_cons {α : Type} {n : ℕ} (a : α) (v : vector α n) (lt : 0 < nat.succ n)
    : vector.nth (vector.cons a v) ⟨0, lt⟩ = a
    := sorry              

lemma all_states_equiv {n : ℕ} (s1 s2 : validstate n) : multi_step s1 s2 :=
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
