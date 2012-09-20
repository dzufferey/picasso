\universalConstants {
  int X_6;
  int X_39;
  int X_14;
  int X_27;
  int X_3;
  int X_5;
  int X_0;
  int X_30;
  int X_10;
  int X_18;
}

\existentialConstants {
  int X_4_pp; 
  int X_5_pp; 
  int X_10_pp; 
  int X_27_pp; 
  int X_1_pp; 
  int X_11_pp; 
  int X_18_pp; 
  int X_2_pp; 
  int X_7_pp; 
  int X_39_pp; 
  int X_30_pp; 
  int X_3_pp; 
  int X_0_pp; 
  int X_14_pp; 
  int X_6_pp; 
}

\problem{
  \exists int
      X_2_p,
      X_5_p,
      X_39_p,
      X_7_p,
      X_27_p,
      X_0_p,
      X_1_p,
      X_6_p,
      X_3_p,
      X_11_p,
      X_14_p,
      X_10_p,
      X_18_p,
      X_4_p,
      X_30_p
  ; (
  0 <= X_6 &
  1 <= X_39 &
  0 <= X_14 &
  0 <= X_27 &
  0 <= X_3 &
  0 <= X_5 &
  0 <= X_0 &
  1 <= X_30 &
  0 <= X_10 &
  0 <= X_18
  ->
    X_2_p = X_10 &
    X_5_p = X_18 &
    X_39_p + X_7_p = X_39 + -1 &
    X_27_p = X_5 &
    X_0_p = X_0 &
    X_1_p + X_6_p = X_6 &
    X_3_p = X_3 &
    X_11_p = X_27 &
    X_14_p + X_10_p = X_14 &
    X_18_p = 1 &
    X_4_p = 1 &
    X_30_p = X_30 + -1 &
    0 <= X_14_p &
    0 <= X_39_p &
    0 <= X_6_p &
    0 <= X_10_p &
    0 <= X_7_p &
    0 <= X_1_p &
    X_4_pp = 0 &
    X_5_pp = X_27_p + X_14_p &
    X_10_pp = X_2_p + X_6_p &
    X_27_pp = X_11_p + 1 &
    X_1_pp = 0 &
    X_11_pp = 0 &
    X_18_pp = X_5_p + X_39_p &
    X_2_pp = 0 &
    X_7_pp = 1 &
    X_39_pp = X_39_p &
    X_30_pp = X_30_p &
    X_3_pp = X_3_p &
    X_0_pp = X_0_p &
    X_14_pp = X_14_p &
    X_6_pp = X_6_p
  )
}

/*

Formula is valid, resulting most-general constraint:
        X_18 + X_39_pp - X_18_pp = 0 &
        X_10 + X_6_pp - X_10_pp = 0 &
        X_30 - X_30_pp = 1 &
        X_0 = X_0_pp &
        X_5 + X_14_pp - X_5_pp = 0 &
        X_3 = X_3_pp &
        X_27 - X_27_pp = -1 &
        X_7_pp = 1 &
        X_2_pp = 0 &
        X_11_pp = 0 &
        X_1_pp = 0 &
        X_4_pp = 0 &
        X_14 >= X_14_pp &
        X_14 >= 0 &
        X_39 - X_39_pp >= 1 &
        X_6 >= X_6_pp &
        X_6 >= 0 &
        X_10_pp >= X_6_pp &
        X_6_pp >= 0 &
        X_5_pp >= X_14_pp &
        X_14_pp >= 0 &
        X_0_pp >= 0 &
        X_3_pp >= 0 &
        X_30_pp >= 0 &
        X_18_pp >= X_39_pp &
        X_39_pp >= 0 &
        X_27_pp >= 1
   =========================
    0 <= X_6 &
    1 <= X_39 &
    0 <= X_14 &
    0 <= X_27 &
    0 <= X_3 &
    0 <= X_5 &
    0 <= X_0 &
    1 <= X_30 &
    0 <= X_10 &
    0 <= X_18
    ->
        X_18_pp - X_39_pp = X_18 &
        x_10_pp - X_6_pp = X_10 &
        x_5_pp - X_14_pp = X_5 &
        X_30_pp = X_30 - 1 &
        X_27_pp = X_27 + 1 &
        X_39_pp <= X_39 - 1 &
        X_0_pp = X_0 &
        X_3_pp = X_3 &
        X_7_pp = 1 &
        X_2_pp = 0 &
        X_11_pp = 0 &
        X_1_pp = 0 &
        X_4_pp = 0 &
        X_14_pp <= X_14 &
        X_6_pp <= X_6 &
        X_6_pp >= 0 &
        X_14_pp >= 0 &
        X_39_pp >= 0 &
*/
