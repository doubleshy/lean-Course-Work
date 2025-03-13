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
  -- **Step 1: Introduce variables and assumptions**
  assume x y z,    -- Assume x, y, z are arbitrary elements of A
  assume hxy,      -- Assume x ≠ y, i.e., ¬(x = y)

  -- **Step 2: Use classical logic (Law of Excluded Middle)**
  cases em (x = z) with hxz hxz,  -- `hxz : x = z` or `hxz : x ≠ z`
  
  -- **Case 1: Assume `x = z`, need to show `y ≠ z`**
  right,        -- Choose the right branch of `∨`, goal is to show `y ≠ z`
  assume hyz,   -- Assume `y = z`, try to derive a contradiction

  -- **Step 3: Derive `x = y` manually**
  cases hxz,    -- Replace x with z using `hxz : x = z`
  cases hyz,    -- Replace y with z using `hyz : y = z`

  -- **Derive contradiction**
  contradiction, -- But `hxy : x ≠ y`, so `x = y` is a contradiction!

  -- **Case 2: Assume `x ≠ z`, directly conclude**
  left,        -- Choose the left branch of `∨`, goal is to show `x ≠ z`
  exact hxz,   -- Directly use `hxz : x ≠ z`
end







theorem ex6q05 : ¬ (∀ x : A, PP x) → ∃ x : A, ¬ PP x :=
begin
  -- **Step 1: Introduce assumption**
  assume h,  -- Assume h : ¬ (∀ x : A, PP x), meaning "not all x satisfy PP x"

  -- **Step 2: Use the Law of Excluded Middle**
  cases em (∃ x : A, ¬ PP x) with hex hex,
  
  -- **Case 1: Assume ∃ x : A, ¬ PP x holds**
  exact hex,  -- Directly use hex as the conclusion

  -- **Case 2: Assume ¬ ∃ x : A, ¬ PP x**
  -- This implies "all x satisfy PP x"
  have hforall : ∀ x : A, PP x,  -- Assume ∀ x, PP x
  assume x,
  by_contradiction hnp,  -- Assume PP x does not hold
  apply hex,             -- But hex is ¬ ∃ x, ¬ PP x
  existsi x,             -- We found an x where PP x does not hold
  exact hnp,             -- This contradicts hex!

  -- **Derive contradiction**
  contradiction,  -- But h : ¬ (∀ x, PP x), contradiction!
end
