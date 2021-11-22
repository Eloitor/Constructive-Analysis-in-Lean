import regular_sequence
import reals

namespace regular_sequence

def mul: regular_sequence → regular_sequence → regular_sequence :=
  λ x y,
  { val := let k := max (canonical_bound x) (canonical_bound y) in 
          λ n, x (2*k*n) * y (2*k*n),
    property := 
    begin
      intros m n m_pos n_pos,
      set kx := canonical_bound x with h_kx,
      set ky := canonical_bound y with h_ky,
      set k := max kx ky with hk,
      simp,

      have k_pos: 0 < k,
        {
          rw hk,
          rw lt_max_iff,
          left,
          rw h_kx,
          unfold canonical_bound,
          simp,
        },
      
      have two_k_m_pos: 0 < 2 * k * m,
        {
          apply nat.mul_pos,
          exact nat.succ_mul_pos 1 k_pos,
          assumption,
        },

      have two_k_n_pos: 0 < 2 * k * n,
        {
          apply nat.mul_pos,
          exact nat.succ_mul_pos 1 k_pos,
          assumption,
        },
      
      have hx := abs_le_canonical_bound x,
      have hy := abs_le_canonical_bound y,
      cases x,
      cases y,
      obtain := x_property two_k_m_pos two_k_n_pos,
      obtain := y_property two_k_m_pos two_k_n_pos,

      change |x_val (2 * k * m) * y_val (2 * k * m) - x_val (2 * k * n) * y_val (2 * k * n)| ≤ (m:ℚ)⁻¹ + (n:ℚ)⁻¹,
      
      calc |x_val (2 * k * m) * y_val (2 * k * m) - (x_val (2 * k * n) * y_val (2 * k * n))|
       = |(x_val (2*k*m)) * (y_val (2*k*m) - y_val (2*k*n)) + (y_val (2*k*n)) * (x_val (2*k*m) - x_val (2*k*n))| : by { congr, ring_nf,}
        ... ≤ |(x_val (2*k*m)) * (y_val (2*k*m) - y_val (2*k*n))| + |(y_val (2*k*n)) * (x_val (2*k*m) - x_val (2*k*n))| : abs_add _ _
        ... ≤ k * |(y_val (2*k*m) - y_val (2*k*n))| + k * |(x_val (2*k*m) - x_val (2*k*n))| : 
        begin 
          apply add_le_add,
          {
            rw abs_mul,
            apply mul_le_mul,
            {
              transitivity (kx:ℚ),
              {
                rw h_kx,
                apply hx (2*k*m) two_k_m_pos,
              },
              {
                rw hk,
                norm_cast,
                exact le_max_left kx ky,
              },
            },
            {
              refl,
            },
            {
              exact abs_nonneg (y_val (2 * k * m) - y_val (2 * k * n)),
            },
            {
              exact nat.cast_nonneg k,
            },
          },
          {
            rw abs_mul,
            apply mul_le_mul,
            {
              transitivity (ky:ℚ),
              {
                rw h_ky,
                apply hy (2*k*n) two_k_n_pos,
              },
              {
                rw hk,
                norm_cast,
                exact le_max_right kx ky,
              },
            },
            {
              refl,
            },
            {
              exact abs_nonneg (x_val (2 * k * m) - x_val (2 * k * n)),
            },
            {
              exact nat.cast_nonneg k,
            },
          },
        end
    
        ... ≤ k*((↑(2 * k * m))⁻¹ + (↑(2 * k * n))⁻¹) + k*((↑(2 * k * m))⁻¹ + (↑(2 * k * n))⁻¹) : 
        begin
          apply add_le_add;
          {
            rw mul_le_mul_left,
            {
              assumption,
            },
            {
              exact nat.cast_pos.mpr k_pos,
            },
          },
        end
       ... = (m: ℚ)⁻¹+ (n:ℚ)⁻¹ : 
       begin
         rw ←mul_add,
         rw add_assoc,
         rw add_comm (↑(2 * k * m))⁻¹ (↑(2 * k * n))⁻¹,
         nth_rewrite 1 ←add_assoc,
         push_cast,
         
         simp,
         ring_nf,
         rw add_mul,
         congr;
          {
            rw mul_comm,
            rw ←mul_assoc,
            simp,
            norm_num;
            rw mul_inv₀,
            rw mul_inv₀,
            nth_rewrite 1 mul_assoc,
            rw mul_assoc,
            nth_rewrite 1 ←mul_assoc,
            simp only [one_mul, mul_inv_cancel, ne.def, not_false_iff, bit0_eq_zero, one_ne_zero],
            rw ←mul_assoc,
            rw mul_inv_cancel,
            {
              simp,
            },
            {
              rw hk at k_pos,
              apply ne_of_gt,
              have := (@nat.cast_pos ℚ _  _ (max kx ky)).mpr,
              push_cast at this,
              exact this k_pos,
            },
          },
       end
    end
  }
  
instance : has_mul regular_sequence :=
  ⟨mul⟩

end regular_sequence

namespace real

def mul: real → real → real :=
  quotient.lift₂ (λ x y, ⟦regular_sequence.mul x y⟧)
  begin
    sorry,
  end

instance : has_mul real :=
  ⟨mul⟩

end real
