
import data.vector

inductive column
| left : column
| middle : column
| right : column

-- okay so we encode valid states as fixed length sequences
def validstate (n : ℕ) := vector column n

def update_nth {n : ℕ} {α : Type} : vector α n → fin n → α → vector α n
| ⟨ [], h ⟩ ⟨ i, _ ⟩ a := begin
    have ofc : n = 0 := begin
        simp at h,
        exact eq.symm h,
    end,
    rw ofc at _x,
    sorry
end
| ⟨ x :: xs, h ⟩ ⟨ nat.zero, _ ⟩ a := ⟨ a :: xs , by { rw ←h, refl } ⟩ 
| v@⟨ x :: xs, h ⟩ ⟨ nat.succ m, pf ⟩ a :=
    vector.cons x (update_nth ⟨ xs , begin
        rw ←h,
        sorry
    end ⟩ ⟨ m, begin
        have ofc : m < nat.succ m := begin
            sorry
        end,
        exact lt_trans ofc pf
    end ⟩  a)

#check fin.succ

lemma update_nth_helper {n : ℕ} {α : Type} (v : vector α n) (i : fin n) (a b : α)
    : vector.cons b (update_nth v i a) = update_nth (vector.cons b v) (fin.succ i) a :=
sorry

def movestone {n : ℕ} (s : validstate n) (i : fin n) (dest : column)
    (valid_move: ∀j, j > i → vector.nth s j ≠ dest ∧ vector.nth s j ≠ vector.nth s i) : validstate n :=
update_nth s i dest

#check list.cons

/-- `refl_trans r`: relexive and transitive closure of `r` -/
inductive refl_trans {α : Sort*} (r : α → α → Prop) (a : α) : α → Prop
| refl {} : refl_trans a
| tail {b c} : refl_trans b → r b c → refl_trans c

def one_step {n : ℕ} : validstate n → validstate n → Prop
| s1 s2 := ∃ (i : fin n) (dest : column) pf, s2 = movestone s1 i dest pf

def multi_step {n : ℕ} : validstate n → validstate n → Prop := refl_trans one_step

lemma one_step_symm {n : ℕ} (s1 s2 : validstate n) : one_step s1 s2 → one_step s2 s1 :=
begin
    intro h,
    cases h,
    cases h_h,
    cases h_h_h,
    simp [movestone, update_nth] at h_h_h_h,
    sorry
end

-- TODO: show that multi_step is symmetric
-- TODO: show that multi_step is transitive

--lemma multi_step_equivalence {n : ℕ}: reflexive multi_step

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

def zero_fin (n : ℕ) : fin (nat.succ n) := ⟨0, sorry⟩ 

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
            sorry
        }
    }
end


lemma all_states_equiv {n : ℕ} (s1 s2 : validstate n) : multi_step s1 s2 :=
begin
    induction n,
    {   
        have s1_eq_s2 : s1 = s2 := begin
            sorry
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
            (vector.cons s2_val_hd (vector.repeat (third_column s1_val_hd s2_val_hd) n_n)) := begin
            rw one_step,
            have zero_lt_succ : 0 < nat.succ n_n := begin sorry end,

            apply exists.intro (zero_fin n_n),
            {
                apply exists.intro s2_val_hd,
                apply exists.intro,
                {
                    refl,
                },
                {
                    intros j h,
                    rw zero_fin at h,
                    sorry -- should be ez contradiction: n < 0
                }
            }            
        end,
        
        apply refl_trans.tail,

        sorry
    }
end

#check fin.

theorem towers_hanoi_solvable : ∀ n : ℕ, multi_step (vector.repeat column.left n) (vector.repeat column.right n) :=
    λ n, all_states_equiv (vector.repeat column.left n) (vector.repeat column.right n)