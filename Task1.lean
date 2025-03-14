variables (A : Type)
variables (RR : A → A → Prop)
variables (PP : A → Prop)  -- Declare PP as a predicate on A



theorem ex6q02 : ∀ x y : A, x = y → RR x y → RR x x :=
begin
  -- **Step 1: Introduce variables and assumptions**
  assume x y,       -- 1. Assume x and y are arbitrary elements of A
  assume hxy,       -- 2. Assume x = y
  assume hrxy,      -- 3. Assume RR x y holds

  -- **Step 2: Use `cases` to replace `y` with `x`**
  cases hxy,        -- Replace `y` with `x` everywhere
  
  -- **Step 3: The goal becomes `RR x x`, use `hrxy` directly**
  exact hrxy,       -- Directly complete the proof
end













open classical

theorem ex6q04 : ∀ x y z : A, x ≠ y → (x ≠ z ∨ y ≠ z) :=
begin
  assume x y z,  -- Step 1: Let x, y, and z be arbitrary elements of A
  assume hxy,    -- Step 2: Assume x ≠ y, which means ¬(x = y)
  cases em (x = z) with hxz hxz,  -- Step 3: Perform case analysis on (x = z)
  
   right, -- Step 4: Choose the right branch of the disjunction (y ≠ z)
    assume hyz, -- Step 5: Assume y = z and try to derive a contradiction
    apply hxy, -- Step 6: Goal is to prove x = y
    rewrite hxz,  -- Step 7: Substitute x = z
    rewrite hyz,  -- Step 8: Substitute y = z, which results in x = y, contradicting hxy
  
   left,  -- Step 9: Choose the left branch of the disjunction (x ≠ z)
    exact hxz,  -- Step 10: Directly use hxz : x ≠ z
end

















variables P  : Prop

constant raa : ¬ ¬ P → P

-- Proving theorem ex6q05
theorem ex6q05 : ¬ (∀ x : A, PP x) → ∃ x : A, ¬ PP x :=
begin
  -- **Step 1: Assume the premise**
  assume h,  -- Assume h : ¬ (∀ x, PP x), meaning "not all x satisfy PP x"

  -- **Step 2: Use raa (reductio ad absurdum)**
  apply raa,  -- Our goal is to prove ∃ x, ¬ PP x, using raa (proof by contradiction)

  -- **Step 3: Assume the negation of the conclusion**
  assume h1,  -- Assume h1 : ¬ (∃ x, ¬ PP x), meaning "there does not exist an x such that ¬ PP x"

  -- **Step 4: Try to derive a contradiction**
  apply h,  -- To derive a contradiction, we attempt to prove ∀ x, PP x

  -- **Step 5: Introduce an arbitrary x**
  assume x,  -- Let x be an arbitrary element of A

  -- **Step 6: Use raa to establish PP x**
  apply raa,  -- Since we need to prove PP x, we use raa: ¬¬ PP x → PP x
  assume h2,  -- Assume h2 : ¬ PP x

  -- **Step 7: Construct a contradiction**
  apply h1,  -- Recall h1 : ¬ (∃ x, ¬ PP x), meaning "there is no x such that ¬ PP x"
  existsi x,  -- However, we have found an x such that ¬ PP x
  exact h2,  -- This contradicts h1, so h1 must be false, proving ∃ x, ¬ PP x
end

