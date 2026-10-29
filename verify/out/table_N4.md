# Section 5 relation defects, N = 4

K_N = [0], theta_N = 0.25, k_N = 2, log2 dim = 3N + k_N = 14, (3+theta_N)N = 13.0
4^-N = 3.906250e-03

| relation | claim | support | op-norm | op*4^N | flat HS | HS*4^N | nnz | status | top state(s) |
|---|---|---|---|---|---|---|---|---|---|
| (3) [A_a,P_a] | EXACT | x |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (3) T_aA_aT_a*-4A_a+3P_a | <= 3 4^-N | xy |  1.172e-02 |  3.000e+00 |  8.286e-03 |  2.121e+00 | 32 | PASS(<=claim) | 1.17e-02@{'x': 3, 'y': 0}; 1.17e-02@{'x': 1, 'y': 3} |
| (3) X_aP_aX_a-(I-P_a) | EXACT | xy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (3) [X_a,T_aA_aT_a*] | <= 3 4^-N | xy |  1.172e-02 |  3.000e+00 |  1.172e-02 |  3.000e+00 | 64 | PASS(<=claim) | 1.17e-02@{'x': 1, 'y': 0}; 1.17e-02@{'x': 0, 'y': 3} |
| (3) [A_f,P_f] | EXACT | q |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (3) T_fA_fT_f*-4A_f+3P_f | <= 3 4^-N | q |  1.172e-02 |  3.000e+00 |  8.286e-03 |  2.121e+00 | 8 | PASS(<=claim) | 1.17e-02@{'q': 9}; 1.17e-02@{'q': 7} |
| (3) X_fP_fX_f-(I-P_f) | EXACT | q |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (3) [X_f,T_fA_fT_f*] | <= 3 4^-N | q |  1.172e-02 |  3.000e+00 |  1.172e-02 |  3.000e+00 | 16 | PASS(<=claim) | 1.17e-02@{'q': 4}; 1.17e-02@{'q': 3} |
| (3) [A_t,P_t] | EXACT | t |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (3) T_tA_tT_t*-4A_t+3P_t | <= 3 4^-N | t |  1.172e-02 |  3.000e+00 |  8.286e-03 |  2.121e+00 | 8 | PASS(<=claim) | 1.17e-02@{'t': 9}; 1.17e-02@{'t': 7} |
| (3) X_tP_tX_t-(I-P_t) | EXACT | t |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (3) [X_t,T_tA_tT_t*] | <= 3 4^-N | t |  1.172e-02 |  3.000e+00 |  1.172e-02 |  3.000e+00 | 16 | PASS(<=claim) | 1.17e-02@{'t': 4}; 1.17e-02@{'t': 3} |
| (4) guarded increment V | <= 1.414 4^-N | xy |  5.524e-03 |  1.414e+00 |  1.381e-03 |  3.536e-01 | 8 | PASS(<=claim) | 5.52e-03@{'x': 15, 'y': 3}; 5.52e-03@{'x': 15, 'y': 2} |
| (4) guarded increment U | <= 1.414 4^-N | t |  5.524e-03 |  1.414e+00 |  1.381e-03 |  3.536e-01 | 2 | PASS(<=claim) | 5.52e-03@{'t': 15} |
| (5) H-(I-P_a)-1/4 P_a T_aHT_a* | EXACT | xy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (5) [P_a,T_aHT_a*] | EXACT | xy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (5) [H,A_a] | EXACT | x |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (6) V*A_aV-A_a+I-7/4H | <= 1 4^-N | xy |  3.906e-03 |  1.000e+00 |  9.766e-04 |  2.500e-01 | 4 | PASS(<=claim) | 3.91e-03@{'x': 15, 'y': 3}; 3.91e-03@{'x': 15, 'y': 2} |
| (7) L-E1-E00 T^2LT^-2 | EXACT | xy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (8) R-(I-E00)-1/2 E00 T^2RT^-2 | EXACT | xy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (7) L^2-L | EXACT | x |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (10) B_0L-B_0 | EXACT | xy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (10) B_0R-2^-0B_0 | EXACT | xy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (10) B_1L-B_1 | EXACT | xy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (10) B_1R-2^-1B_1 | EXACT | xy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (11) Z-(I-P_f)-P_f(I-P_t)SZS* | EXACT | qt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (11) Z^2-Z | EXACT | qt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (12) C_0Z-C_0D_0 | EXACT | qt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (12) C_1Z-C_1D_1 | EXACT | qt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (12) C_2Z-C_2D_2 | EXACT | qt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (12) C_3Z-C_3D_3 | EXACT | qt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (13) r1-z1-1/2(I-z1)s1 | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (13) z1^2-z1 | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (13) r2-z2-1/2(I-z2)s2 | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (13) z2^2-z2 | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (13) r3-z3-1/2(I-z3)s3 | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (13) z3^2-z3 | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (14) ZW-Z Init(W), W=q_start | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (14) ZW-Z Init(W), W=q_z0 | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (14) ZW-Z Init(W), W=q_z1 | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (14) ZW-Z Init(W), W=q_z2 | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (14) ZW-Z Init(W), W=q_d1 | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (14) ZW-Z Init(W), W=q_loop | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (14) ZW-Z Init(W), W=q_g0 | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (14) ZW-Z Init(W), W=q_g1 | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (14) ZW-Z Init(W), W=q_g2 | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (14) ZW-Z Init(W), W=q_mc | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (14) ZW-Z Init(W), W=q_ma | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (14) ZW-Z Init(W), W=q_mb1 | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (14) ZW-Z Init(W), W=q_mb2 | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (14) ZW-Z Init(W), W=q_mb3 | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (14) ZW-Z Init(W), W=q_mb4 | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (14) ZW-Z Init(W), W=q_bk | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (14) ZW-Z Init(W), W=q_bi | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (14) ZW-Z Init(W), W=q_cnt | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (14) ZW-Z Init(W), W=q_halt | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (14) ZW-Z Init(W), W=q_idle | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (14) ZW-Z Init(W), W=r1 | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (14) ZW-Z Init(W), W=r2 | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (14) ZW-Z Init(W), W=r3 | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (15) U*WU-Z+Init-(I-Z+)Step, W=q_start | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (15) U*WU-Z+Init-(I-Z+)Step, W=q_z0 | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (15) U*WU-Z+Init-(I-Z+)Step, W=q_z1 | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (15) U*WU-Z+Init-(I-Z+)Step, W=q_z2 | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (15) U*WU-Z+Init-(I-Z+)Step, W=q_d1 | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (15) U*WU-Z+Init-(I-Z+)Step, W=q_loop | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (15) U*WU-Z+Init-(I-Z+)Step, W=q_g0 | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (15) U*WU-Z+Init-(I-Z+)Step, W=q_g1 | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (15) U*WU-Z+Init-(I-Z+)Step, W=q_g2 | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (15) U*WU-Z+Init-(I-Z+)Step, W=q_mc | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (15) U*WU-Z+Init-(I-Z+)Step, W=q_ma | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (15) U*WU-Z+Init-(I-Z+)Step, W=q_mb1 | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (15) U*WU-Z+Init-(I-Z+)Step, W=q_mb2 | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (15) U*WU-Z+Init-(I-Z+)Step, W=q_mb3 | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (15) U*WU-Z+Init-(I-Z+)Step, W=q_mb4 | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (15) U*WU-Z+Init-(I-Z+)Step, W=q_bk | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (15) U*WU-Z+Init-(I-Z+)Step, W=q_bi | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (15) U*WU-Z+Init-(I-Z+)Step, W=q_cnt | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (15) U*WU-Z+Init-(I-Z+)Step, W=q_halt | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (15) U*WU-Z+Init-(I-Z+)Step, W=q_idle | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (15) U*WU-Z+Init-(I-Z+)Step, W=r1 | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (15) U*WU-Z+Init-(I-Z+)Step, W=r2 | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (15) U*WU-Z+Init-(I-Z+)Step, W=r3 | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| q_start^2-q_start | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| q_z0^2-q_z0 | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| q_z1^2-q_z1 | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| q_z2^2-q_z2 | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| q_d1^2-q_d1 | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| q_loop^2-q_loop | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| q_g0^2-q_g0 | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| q_g1^2-q_g1 | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| q_g2^2-q_g2 | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| q_mc^2-q_mc | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| q_ma^2-q_ma | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| q_mb1^2-q_mb1 | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| q_mb2^2-q_mb2 | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| q_mb3^2-q_mb3 | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| q_mb4^2-q_mb4 | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| q_bk^2-q_bk | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| q_bi^2-q_bi | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| q_cnt^2-q_cnt | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| q_halt^2-q_halt | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| q_idle^2-q_idle | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| sum_sigma q_sigma - I | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (16) (I-F) q_halt | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (21) (I-F)Q  [Q<=F] | EXACT | xy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (21) [B,Q] | EXACT | xy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (21) [B,F] | EXACT | xy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (21) [C,Q] | EXACT | xy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (21) [C,F] | EXACT | xy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (21) [B,C] | EXACT | xy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (22) VBV*-4B+3Q | EXACT(series) | xy |          0 |          0 |          0 |          0 | 0 | PASS(<=1e-15) |  |
| (22) VCV*-4C+3F | EXACT(series) | xy |          0 |          0 |          0 |          0 | 0 | PASS(<=1e-15) |  |
| (23) YFY-F | EXACT | xy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (23) YQY-(F-Q) | EXACT | xy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (24) [Y,VBV*]  (est. 32) | <= 2 4^-N | xy |  4.578e-05 |  1.172e-02 |  2.289e-05 |  5.859e-03 | 16 | PASS(<=claim) | 4.58e-05@{'x': 13, 'y': 1}; 4.58e-05@{'x': 5, 'y': 1} |
| (24) [Y,C] | EXACT | xy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (23) Y^2-I | EXACT | xy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| Q^2-Q | EXACT | xy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| F^2-F | EXACT | x |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| T_a*T_a-I | EXACT | xy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| T_aT_a*-I | EXACT | xy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| X_a*X_a-I | EXACT | xy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| X_aX_a*-I | EXACT | xy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| T_f*T_f-I | EXACT | q |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| T_fT_f*-I | EXACT | q |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| X_f*X_f-I | EXACT | q |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| X_fX_f*-I | EXACT | q |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| T_t*T_t-I | EXACT | t |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| T_tT_t*-I | EXACT | t |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| X_t*X_t-I | EXACT | t |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| X_tX_t*-I | EXACT | t |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| V*V-I | EXACT | xy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| VV*-I | EXACT | xy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| U*U-I | EXACT | t |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| UU*-I | EXACT | t |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| Y*Y-I | EXACT | xy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| YY*-I | EXACT | xy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| X_a^2-I | EXACT | xy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| X_a-X_a* | EXACT | xy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| X_f^2-I | EXACT | q |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| X_f-X_f* | EXACT | q |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| X_t^2-I | EXACT | t |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| X_t-X_t* | EXACT | t |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| Y^2-I | EXACT | xy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| Y-Y* | EXACT | xy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| P_a^2-P_a | EXACT | x |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| P_f^2-P_f | EXACT | q |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| P_t^2-P_t | EXACT | t |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5a [L,R] | EXACT | x |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5a [L,F] | EXACT | x |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5a [L,A_a] | EXACT | x |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5a [L,A_f] | EXACT | xq |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5a [L,P_f] | EXACT | xq |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5a [L,T_f] | EXACT | xq |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5a [L,X_f] | EXACT | xq |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5a [L,A_t] | EXACT | xt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5a [L,P_t] | EXACT | xt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5a [L,T_t] | EXACT | xt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5a [L,X_t] | EXACT | xt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5a [L,U] | EXACT | xt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5a [R,F] | EXACT | x |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5a [R,A_a] | EXACT | x |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5a [R,A_f] | EXACT | xq |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5a [R,P_f] | EXACT | xq |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5a [R,T_f] | EXACT | xq |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5a [R,X_f] | EXACT | xq |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5a [R,A_t] | EXACT | xt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5a [R,P_t] | EXACT | xt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5a [R,T_t] | EXACT | xt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5a [R,X_t] | EXACT | xt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5a [R,U] | EXACT | xt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5a [F,A_a] | EXACT | x |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5a [F,A_f] | EXACT | xq |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5a [F,P_f] | EXACT | xq |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5a [F,T_f] | EXACT | xq |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5a [F,X_f] | EXACT | xq |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5a [F,A_t] | EXACT | xt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5a [F,P_t] | EXACT | xt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5a [F,T_t] | EXACT | xt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5a [F,X_t] | EXACT | xt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5a [F,U] | EXACT | xt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [Z,q_start] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [Z,q_z0] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [Z,q_z1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [Z,q_z2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [Z,q_d1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [Z,q_loop] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [Z,q_g0] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [Z,q_g1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [Z,q_g2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [Z,q_mc] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [Z,q_ma] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [Z,q_mb1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [Z,q_mb2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [Z,q_mb3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [Z,q_mb4] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [Z,q_bk] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [Z,q_bi] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [Z,q_cnt] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [Z,q_halt] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [Z,q_idle] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [Z,r1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [Z,r2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [Z,r3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [Z,z1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [Z,z2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [Z,z3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [Z,s1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [Z,s2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [Z,s3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [Z,A_a] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [Z,A_f] | EXACT | qt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [Z,A_t] | EXACT | qt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [Z,L] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [Z,R] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [Z,F] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_start,q_z0] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_start,q_z1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_start,q_z2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_start,q_d1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_start,q_loop] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_start,q_g0] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_start,q_g1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_start,q_g2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_start,q_mc] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_start,q_ma] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_start,q_mb1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_start,q_mb2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_start,q_mb3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_start,q_mb4] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_start,q_bk] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_start,q_bi] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_start,q_cnt] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_start,q_halt] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_start,q_idle] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_start,r1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_start,r2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_start,r3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_start,z1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_start,z2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_start,z3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_start,s1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_start,s2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_start,s3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_start,A_a] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_start,A_f] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_start,A_t] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_start,L] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_start,R] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_start,F] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z0,q_z1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z0,q_z2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z0,q_d1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z0,q_loop] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z0,q_g0] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z0,q_g1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z0,q_g2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z0,q_mc] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z0,q_ma] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z0,q_mb1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z0,q_mb2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z0,q_mb3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z0,q_mb4] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z0,q_bk] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z0,q_bi] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z0,q_cnt] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z0,q_halt] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z0,q_idle] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z0,r1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z0,r2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z0,r3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z0,z1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z0,z2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z0,z3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z0,s1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z0,s2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z0,s3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z0,A_a] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z0,A_f] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z0,A_t] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z0,L] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z0,R] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z0,F] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z1,q_z2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z1,q_d1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z1,q_loop] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z1,q_g0] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z1,q_g1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z1,q_g2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z1,q_mc] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z1,q_ma] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z1,q_mb1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z1,q_mb2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z1,q_mb3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z1,q_mb4] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z1,q_bk] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z1,q_bi] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z1,q_cnt] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z1,q_halt] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z1,q_idle] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z1,r1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z1,r2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z1,r3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z1,z1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z1,z2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z1,z3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z1,s1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z1,s2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z1,s3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z1,A_a] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z1,A_f] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z1,A_t] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z1,L] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z1,R] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z1,F] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z2,q_d1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z2,q_loop] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z2,q_g0] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z2,q_g1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z2,q_g2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z2,q_mc] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z2,q_ma] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z2,q_mb1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z2,q_mb2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z2,q_mb3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z2,q_mb4] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z2,q_bk] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z2,q_bi] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z2,q_cnt] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z2,q_halt] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z2,q_idle] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z2,r1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z2,r2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z2,r3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z2,z1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z2,z2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z2,z3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z2,s1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z2,s2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z2,s3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z2,A_a] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z2,A_f] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z2,A_t] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z2,L] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z2,R] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_z2,F] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_d1,q_loop] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_d1,q_g0] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_d1,q_g1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_d1,q_g2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_d1,q_mc] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_d1,q_ma] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_d1,q_mb1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_d1,q_mb2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_d1,q_mb3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_d1,q_mb4] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_d1,q_bk] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_d1,q_bi] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_d1,q_cnt] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_d1,q_halt] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_d1,q_idle] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_d1,r1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_d1,r2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_d1,r3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_d1,z1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_d1,z2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_d1,z3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_d1,s1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_d1,s2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_d1,s3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_d1,A_a] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_d1,A_f] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_d1,A_t] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_d1,L] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_d1,R] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_d1,F] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_loop,q_g0] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_loop,q_g1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_loop,q_g2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_loop,q_mc] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_loop,q_ma] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_loop,q_mb1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_loop,q_mb2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_loop,q_mb3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_loop,q_mb4] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_loop,q_bk] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_loop,q_bi] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_loop,q_cnt] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_loop,q_halt] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_loop,q_idle] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_loop,r1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_loop,r2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_loop,r3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_loop,z1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_loop,z2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_loop,z3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_loop,s1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_loop,s2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_loop,s3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_loop,A_a] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_loop,A_f] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_loop,A_t] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_loop,L] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_loop,R] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_loop,F] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g0,q_g1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g0,q_g2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g0,q_mc] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g0,q_ma] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g0,q_mb1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g0,q_mb2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g0,q_mb3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g0,q_mb4] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g0,q_bk] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g0,q_bi] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g0,q_cnt] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g0,q_halt] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g0,q_idle] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g0,r1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g0,r2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g0,r3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g0,z1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g0,z2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g0,z3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g0,s1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g0,s2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g0,s3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g0,A_a] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g0,A_f] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g0,A_t] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g0,L] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g0,R] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g0,F] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g1,q_g2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g1,q_mc] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g1,q_ma] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g1,q_mb1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g1,q_mb2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g1,q_mb3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g1,q_mb4] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g1,q_bk] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g1,q_bi] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g1,q_cnt] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g1,q_halt] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g1,q_idle] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g1,r1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g1,r2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g1,r3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g1,z1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g1,z2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g1,z3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g1,s1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g1,s2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g1,s3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g1,A_a] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g1,A_f] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g1,A_t] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g1,L] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g1,R] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g1,F] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g2,q_mc] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g2,q_ma] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g2,q_mb1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g2,q_mb2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g2,q_mb3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g2,q_mb4] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g2,q_bk] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g2,q_bi] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g2,q_cnt] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g2,q_halt] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g2,q_idle] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g2,r1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g2,r2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g2,r3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g2,z1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g2,z2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g2,z3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g2,s1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g2,s2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g2,s3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g2,A_a] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g2,A_f] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g2,A_t] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g2,L] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g2,R] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_g2,F] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mc,q_ma] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mc,q_mb1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mc,q_mb2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mc,q_mb3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mc,q_mb4] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mc,q_bk] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mc,q_bi] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mc,q_cnt] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mc,q_halt] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mc,q_idle] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mc,r1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mc,r2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mc,r3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mc,z1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mc,z2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mc,z3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mc,s1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mc,s2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mc,s3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mc,A_a] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mc,A_f] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mc,A_t] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mc,L] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mc,R] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mc,F] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_ma,q_mb1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_ma,q_mb2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_ma,q_mb3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_ma,q_mb4] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_ma,q_bk] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_ma,q_bi] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_ma,q_cnt] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_ma,q_halt] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_ma,q_idle] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_ma,r1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_ma,r2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_ma,r3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_ma,z1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_ma,z2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_ma,z3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_ma,s1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_ma,s2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_ma,s3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_ma,A_a] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_ma,A_f] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_ma,A_t] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_ma,L] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_ma,R] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_ma,F] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb1,q_mb2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb1,q_mb3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb1,q_mb4] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb1,q_bk] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb1,q_bi] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb1,q_cnt] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb1,q_halt] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb1,q_idle] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb1,r1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb1,r2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb1,r3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb1,z1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb1,z2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb1,z3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb1,s1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb1,s2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb1,s3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb1,A_a] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb1,A_f] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb1,A_t] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb1,L] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb1,R] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb1,F] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb2,q_mb3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb2,q_mb4] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb2,q_bk] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb2,q_bi] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb2,q_cnt] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb2,q_halt] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb2,q_idle] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb2,r1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb2,r2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb2,r3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb2,z1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb2,z2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb2,z3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb2,s1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb2,s2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb2,s3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb2,A_a] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb2,A_f] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb2,A_t] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb2,L] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb2,R] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb2,F] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb3,q_mb4] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb3,q_bk] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb3,q_bi] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb3,q_cnt] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb3,q_halt] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb3,q_idle] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb3,r1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb3,r2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb3,r3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb3,z1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb3,z2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb3,z3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb3,s1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb3,s2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb3,s3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb3,A_a] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb3,A_f] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb3,A_t] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb3,L] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb3,R] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb3,F] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb4,q_bk] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb4,q_bi] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb4,q_cnt] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb4,q_halt] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb4,q_idle] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb4,r1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb4,r2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb4,r3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb4,z1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb4,z2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb4,z3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb4,s1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb4,s2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb4,s3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb4,A_a] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb4,A_f] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb4,A_t] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb4,L] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb4,R] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_mb4,F] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_bk,q_bi] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_bk,q_cnt] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_bk,q_halt] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_bk,q_idle] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_bk,r1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_bk,r2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_bk,r3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_bk,z1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_bk,z2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_bk,z3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_bk,s1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_bk,s2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_bk,s3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_bk,A_a] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_bk,A_f] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_bk,A_t] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_bk,L] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_bk,R] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_bk,F] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_bi,q_cnt] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_bi,q_halt] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_bi,q_idle] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_bi,r1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_bi,r2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_bi,r3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_bi,z1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_bi,z2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_bi,z3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_bi,s1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_bi,s2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_bi,s3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_bi,A_a] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_bi,A_f] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_bi,A_t] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_bi,L] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_bi,R] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_bi,F] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_cnt,q_halt] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_cnt,q_idle] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_cnt,r1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_cnt,r2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_cnt,r3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_cnt,z1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_cnt,z2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_cnt,z3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_cnt,s1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_cnt,s2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_cnt,s3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_cnt,A_a] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_cnt,A_f] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_cnt,A_t] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_cnt,L] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_cnt,R] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_cnt,F] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_halt,q_idle] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_halt,r1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_halt,r2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_halt,r3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_halt,z1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_halt,z2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_halt,z3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_halt,s1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_halt,s2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_halt,s3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_halt,A_a] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_halt,A_f] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_halt,A_t] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_halt,L] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_halt,R] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_halt,F] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_idle,r1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_idle,r2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_idle,r3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_idle,z1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_idle,z2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_idle,z3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_idle,s1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_idle,s2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_idle,s3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_idle,A_a] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_idle,A_f] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_idle,A_t] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_idle,L] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_idle,R] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [q_idle,F] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [r1,r2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [r1,r3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [r1,z1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [r1,z2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [r1,z3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [r1,s1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [r1,s2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [r1,s3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [r1,A_a] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [r1,A_f] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [r1,A_t] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [r1,L] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [r1,R] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [r1,F] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [r2,r3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [r2,z1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [r2,z2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [r2,z3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [r2,s1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [r2,s2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [r2,s3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [r2,A_a] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [r2,A_f] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [r2,A_t] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [r2,L] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [r2,R] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [r2,F] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [r3,z1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [r3,z2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [r3,z3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [r3,s1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [r3,s2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [r3,s3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [r3,A_a] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [r3,A_f] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [r3,A_t] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [r3,L] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [r3,R] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [r3,F] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [z1,z2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [z1,z3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [z1,s1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [z1,s2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [z1,s3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [z1,A_a] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [z1,A_f] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [z1,A_t] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [z1,L] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [z1,R] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [z1,F] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [z2,z3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [z2,s1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [z2,s2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [z2,s3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [z2,A_a] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [z2,A_f] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [z2,A_t] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [z2,L] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [z2,R] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [z2,F] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [z3,s1] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [z3,s2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [z3,s3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [z3,A_a] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [z3,A_f] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [z3,A_t] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [z3,L] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [z3,R] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [z3,F] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [s1,s2] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [s1,s3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [s1,A_a] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [s1,A_f] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [s1,A_t] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [s1,L] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [s1,R] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [s1,F] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [s2,s3] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [s2,A_a] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [s2,A_f] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [s2,A_t] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [s2,L] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [s2,R] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [s2,F] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [s3,A_a] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [s3,A_f] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [s3,A_t] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [s3,L] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [s3,R] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5b [s3,F] | EXACT | xqt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5c [A_a,A_f] | EXACT | xq |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5c [A_a,P_f] | EXACT | xq |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5c [A_a,T_f] | EXACT | xq |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5c [A_a,X_f] | EXACT | xq |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5c [A_a,A_t] | EXACT | xt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5c [A_a,P_t] | EXACT | xt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5c [A_a,T_t] | EXACT | xt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5c [A_a,X_t] | EXACT | xt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5c [A_a,U] | EXACT | xt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5c [P_a,A_f] | EXACT | xq |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5c [P_a,P_f] | EXACT | xq |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5c [P_a,T_f] | EXACT | xq |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5c [P_a,X_f] | EXACT | xq |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5c [P_a,A_t] | EXACT | xt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5c [P_a,P_t] | EXACT | xt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5c [P_a,T_t] | EXACT | xt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5c [P_a,X_t] | EXACT | xt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5c [P_a,U] | EXACT | xt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5c [T_a,A_f] | EXACT | xqy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5c [T_a,P_f] | EXACT | xqy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5c [T_a,T_f] | EXACT | xqy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5c [T_a,X_f] | EXACT | xqy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5c [T_a,A_t] | EXACT | xty |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5c [T_a,P_t] | EXACT | xty |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5c [T_a,T_t] | EXACT | xty |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5c [T_a,X_t] | EXACT | xty |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5c [T_a,U] | EXACT | xty |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5c [X_a,A_f] | EXACT | xqy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5c [X_a,P_f] | EXACT | xqy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5c [X_a,T_f] | EXACT | xqy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5c [X_a,X_f] | EXACT | xqy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5c [X_a,A_t] | EXACT | xty |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5c [X_a,P_t] | EXACT | xty |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5c [X_a,T_t] | EXACT | xty |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5c [X_a,X_t] | EXACT | xty |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5c [X_a,U] | EXACT | xty |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5c [V,A_f] | EXACT | xqy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5c [V,P_f] | EXACT | xqy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5c [V,T_f] | EXACT | xqy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5c [V,X_f] | EXACT | xqy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5c [V,A_t] | EXACT | xty |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5c [V,P_t] | EXACT | xty |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5c [V,T_t] | EXACT | xty |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5c [V,X_t] | EXACT | xty |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5c [V,U] | EXACT | xty |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5c [H,A_f] | EXACT | xq |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5c [H,P_f] | EXACT | xq |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5c [H,T_f] | EXACT | xq |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5c [H,X_f] | EXACT | xq |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5c [H,A_t] | EXACT | xt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5c [H,P_t] | EXACT | xt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5c [H,T_t] | EXACT | xt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5c [H,X_t] | EXACT | xt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 2.5c [H,U] | EXACT | xt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (3) [A_f,A_t] (clocks commute) | EXACT | qt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (3) [A_f,P_t] (clocks commute) | EXACT | qt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (3) [A_f,T_t] (clocks commute) | EXACT | qt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (3) [A_f,X_t] (clocks commute) | EXACT | qt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (3) [A_f,U] (clocks commute) | EXACT | qt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (3) [P_f,A_t] (clocks commute) | EXACT | qt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (3) [P_f,P_t] (clocks commute) | EXACT | qt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (3) [P_f,T_t] (clocks commute) | EXACT | qt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (3) [P_f,X_t] (clocks commute) | EXACT | qt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (3) [P_f,U] (clocks commute) | EXACT | qt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (3) [T_f,A_t] (clocks commute) | EXACT | qt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (3) [T_f,P_t] (clocks commute) | EXACT | qt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (3) [T_f,T_t] (clocks commute) | EXACT | qt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (3) [T_f,X_t] (clocks commute) | EXACT | qt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (3) [T_f,U] (clocks commute) | EXACT | qt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (3) [X_f,A_t] (clocks commute) | EXACT | qt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (3) [X_f,P_t] (clocks commute) | EXACT | qt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (3) [X_f,T_t] (clocks commute) | EXACT | qt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (3) [X_f,X_t] (clocks commute) | EXACT | qt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| (3) [X_f,U] (clocks commute) | EXACT | qt |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 4 [B,A_a] | EXACT | xy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 4 [B,A_f] | EXACT | xqy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 4 [B,P_f] | EXACT | xqy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 4 [B,T_f] | EXACT | xqy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 4 [B,X_f] | EXACT | xqy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 4 [B,A_t] | EXACT | xty |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 4 [B,P_t] | EXACT | xty |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 4 [B,T_t] | EXACT | xty |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 4 [B,X_t] | EXACT | xty |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 4 [B,U] | EXACT | xty |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 4 [C,A_a] | EXACT | xy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 4 [C,A_f] | EXACT | xqy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 4 [C,P_f] | EXACT | xqy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 4 [C,T_f] | EXACT | xqy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 4 [C,X_f] | EXACT | xqy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 4 [C,A_t] | EXACT | xty |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 4 [C,P_t] | EXACT | xty |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 4 [C,T_t] | EXACT | xty |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 4 [C,X_t] | EXACT | xty |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 4 [C,U] | EXACT | xty |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 4 [Q,A_a] | EXACT | xy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 4 [Q,A_f] | EXACT | xqy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 4 [Q,P_f] | EXACT | xqy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 4 [Q,T_f] | EXACT | xqy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 4 [Q,X_f] | EXACT | xqy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 4 [Q,A_t] | EXACT | xty |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 4 [Q,P_t] | EXACT | xty |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 4 [Q,T_t] | EXACT | xty |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 4 [Q,X_t] | EXACT | xty |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 4 [Q,U] | EXACT | xty |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 4 [Y,A_a] | EXACT | xy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 4 [Y,A_f] | EXACT | xqy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 4 [Y,P_f] | EXACT | xqy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 4 [Y,T_f] | EXACT | xqy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 4 [Y,X_f] | EXACT | xqy |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 4 [Y,A_t] | EXACT | xty |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 4 [Y,P_t] | EXACT | xty |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 4 [Y,T_t] | EXACT | xty |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 4 [Y,X_t] | EXACT | xty |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |
| 4 [Y,U] | EXACT | xty |          0 |          0 |          0 |          0 | 0 | PASS(exact 0) |  |

Exact integer check of the series relations (22):
```
{
 "B": {
  "states": 64,
  "period": 16,
  "exact_failures": 0,
  "float_dev": 1.0449157878825003e-17
 },
 "C": {
  "states": 64,
  "period": 16,
  "exact_failures": 0,
  "float_dev": 1.0449157878825003e-17
 }
}
```
