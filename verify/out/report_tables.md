## dims
| N | K_N | theta_N | max window | k_N | N theta_N | k_N - N theta_N | log2 dim = 3N + k_N | (3+theta_N) N | V order | basis states (x,q,t) with q_halt=1 | q_halt<=F violations |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 4 | [0] | 0.25 | 1 | 2 | 1 | 1 | 14 | 13 | 16 | 56 | 0 |
| 6 | [0] | 0.25 | 2 | 3 | 1.5 | 1.5 | 21 | 19.5 | 192 | 4064 | 0 |
| 8 | [0, 2] | 0.265625 | 3 | 4 | 2.125 | 1.875 | 28 | 26.12 | 256 | 262936 | 0 |

## consolidated
| relation (or family) | claimed | # N=4/6/8 | N=4 op*4^N | N=4 HS*4^N | N=6 op*4^N | N=6 HS*4^N | N=8 op*4^N | N=8 HS*4^N | all pass |
|---|---|---|---|---|---|---|---|---|---|
| (3) [A_a,P_a] | EXACT | 1/1/1 | 0 | 0 | 0 | 0 | 0 | 0 | yes |
| (3) T_aA_aT_a*-4A_a+3P_a | <= 3 | 1/1/1 | 3 | 2.121 | 3 | 2.121 | 3 | 2.121 | yes |
| (3) X_aP_aX_a-(I-P_a) | EXACT | 1/1/1 | 0 | 0 | 0 | 0 | 0 | 0 | yes |
| (3) [X_a,T_aA_aT_a*] | <= 3 | 1/1/1 | 3 | 3 | 3 | 3 | 3 | 3 | yes |
| (3) [A_f,P_f] | EXACT | 1/1/1 | 0 | 0 | 0 | 0 | 0 | 0 | yes |
| (3) T_fA_fT_f*-4A_f+3P_f | <= 3 | 1/1/1 | 3 | 2.121 | 3 | 2.121 | 3 | 2.121 | yes |
| (3) X_fP_fX_f-(I-P_f) | EXACT | 1/1/1 | 0 | 0 | 0 | 0 | 0 | 0 | yes |
| (3) [X_f,T_fA_fT_f*] | <= 3 | 1/1/1 | 3 | 3 | 3 | 3 | 3 | 3 | yes |
| (3) [A_t,P_t] | EXACT | 1/1/1 | 0 | 0 | 0 | 0 | 0 | 0 | yes |
| (3) T_tA_tT_t*-4A_t+3P_t | <= 3 | 1/1/1 | 3 | 2.121 | 3 | 2.121 | 3 | 2.121 | yes |
| (3) X_tP_tX_t-(I-P_t) | EXACT | 1/1/1 | 0 | 0 | 0 | 0 | 0 | 0 | yes |
| (3) [X_t,T_tA_tT_t*] | <= 3 | 1/1/1 | 3 | 3 | 3 | 3 | 3 | 3 | yes |
| (4) guarded increment V | <= 1.414 | 1/1/1 | 1.414 | 0.3536 | 1.414 | 0.1768 | 1.414 | 0.08839 | yes |
| (4) guarded increment U | <= 1.414 | 1/1/1 | 1.414 | 0.3536 | 1.414 | 0.1768 | 1.414 | 0.08839 | yes |
| (5) H-(I-P_a)-1/4 P_a T_aHT_a* | EXACT | 1/1/1 | 0 | 0 | 0 | 0 | 0 | 0 | yes |
| (5) [P_a,T_aHT_a*] | EXACT | 1/1/1 | 0 | 0 | 0 | 0 | 0 | 0 | yes |
| (5) [H,A_a] | EXACT | 1/1/1 | 0 | 0 | 0 | 0 | 0 | 0 | yes |
| (6) V*A_aV-A_a+I-7/4H | <= 1 | 1/1/1 | 1 | 0.25 | 1 | 0.125 | 1 | 0.0625 | yes |
| (7) L-E1-E00 T^2LT^-2 | EXACT | 1/1/1 | 0 | 0 | 0 | 0 | 0 | 0 | yes |
| (8) R-(I-E00)-1/2 E00 T^2RT^-2 | EXACT | 1/1/1 | 0 | 0 | 0 | 0 | 0 | 0 | yes |
| domain: projections P_a,P_f,P_t,L,Z,Q,F | EXACT | 7/7/7 | 0 | 0 | 0 | 0 | 0 | 0 | yes |
| (10) B_e L - B_e, every e < N/2 | EXACT | 2/3/4 | 0 | 0 | 0 | 0 | 0 | 0 | yes |
| (10) B_e R - 2^-e B_e, every e < N/2 | EXACT | 2/3/4 | 0 | 0 | 0 | 0 | 0 | 0 | yes |
| (11) Z-(I-P_f)-P_f(I-P_t)SZS* | EXACT | 1/1/1 | 0 | 0 | 0 | 0 | 0 | 0 | yes |
| (12) C_k Z - C_k D_k, every k < N | EXACT | 4/6/8 | 0 | 0 | 0 | 0 | 0 | 0 | yes |
| (13) r_i - z_i - (1/2)(I - z_i) s_i, i = 1,2,3 | EXACT | 3/3/3 | 0 | 0 | 0 | 0 | 0 | 0 | yes |
| domain: z_i projections | EXACT | 3/3/3 | 0 | 0 | 0 | 0 | 0 | 0 | yes |
| (14) Z W - Z Init(W), all 23 W (20 controls, 3 counters) | EXACT | 23/23/23 | 0 | 0 | 0 | 0 | 0 | 0 | yes |
| (15) U*WU - Z+ Init(W) - (I-Z+) Step(W), all 23 W | EXACT | 23/23/23 | 0 | 0 | 0 | 0 | 0 | 0 | yes |
| domain: q_sigma projections | EXACT | 20/20/20 | 0 | 0 | 0 | 0 | 0 | 0 | yes |
| domain: sum_sigma q_sigma = I | EXACT | 1/1/1 | 0 | 0 | 0 | 0 | 0 | 0 | yes |
| (16) (I-F) q_halt | EXACT | 1/1/1 | 0 | 0 | 0 | 0 | 0 | 0 | yes |
| (21) (I-F)Q  [Q<=F] | EXACT | 1/1/1 | 0 | 0 | 0 | 0 | 0 | 0 | yes |
| (21) [B,Q] | EXACT | 1/1/1 | 0 | 0 | 0 | 0 | 0 | 0 | yes |
| (21) [B,F] | EXACT | 1/1/1 | 0 | 0 | 0 | 0 | 0 | 0 | yes |
| (21) [C,Q] | EXACT | 1/1/1 | 0 | 0 | 0 | 0 | 0 | 0 | yes |
| (21) [C,F] | EXACT | 1/1/1 | 0 | 0 | 0 | 0 | 0 | 0 | yes |
| (21) [B,C] | EXACT | 1/1/1 | 0 | 0 | 0 | 0 | 0 | 0 | yes |
| (22) VBV*-4B+3Q | EXACT(series) | 1/1/1 | 0 | 0 | 0 | 0 | 0 | 0 | yes |
| (22) VCV*-4C+3F | EXACT(series) | 1/1/1 | 0 | 0 | 0 | 0 | 0 | 0 | yes |
| (23) YFY-F | EXACT | 1/1/1 | 0 | 0 | 0 | 0 | 0 | 0 | yes |
| (23) YQY-(F-Q) | EXACT | 1/1/1 | 0 | 0 | 0 | 0 | 0 | 0 | yes |
| (24) [Y,VBV*]  (est. 32) | <= 2 | 1/1/1 | 0.01172 | 0.005859 | 0.0007324 | 0.0003662 | 0.01172 | 0.002564 | yes |
| (24) [Y,C] | EXACT | 1/1/1 | 0 | 0 | 0 | 0 | 0 | 0 | yes |
| domain: self-adjoint involutions X_a,X_f,X_t,Y | EXACT | 9/9/9 | 0 | 0 | 0 | 0 | 0 | 0 | yes |
| domain: unitarity (W*W = WW* = I) | EXACT | 18/18/18 | 0 | 0 | 0 | 0 | 0 | 0 | yes |
| 2.5: L,R,F pairwise, with A_a, with all fuel/time clock vars incl. U | EXACT | 33/33/33 | 0 | 0 | 0 | 0 | 0 | 0 | yes |
| 2.5: Z + workspace pairwise, and with A_a,A_f,A_t,L,R,F | EXACT | 615/615/615 | 0 | 0 | 0 | 0 | 0 | 0 | yes |
| 2.5: address set {A_a,P_a,T_a,X_a,V,H} with fuel and time sets | EXACT | 54/54/54 | 0 | 0 | 0 | 0 | 0 | 0 | yes |
| (3): fuel set with time set | EXACT | 20/20/20 | 0 | 0 | 0 | 0 | 0 | 0 | yes |
| Sec. 4: B,C,Q,Y with A_a and all fuel/time clock vars | EXACT | 40/40/40 | 0 | 0 | 0 | 0 | 0 | 0 | yes |

## nonzero
| N | relation | op-norm | op*4^N | flat HS | nnz | op-norm method | largest-defect basis states |
|---|---|---|---|---|---|---|---|
| 4 | (3) T_aA_aT_a*-4A_a+3P_a | 1.171875e-02 | 3 | 8.2864e-03 | 32 | diagonal | {'x': 3, 'y': 0}; {'x': 1, 'y': 3} |
| 4 | (3) [X_a,T_aA_aT_a*] | 1.171875e-02 | 3 | 1.1719e-02 | 64 | dense-svd | {'x': 1, 'y': 0}; {'x': 0, 'y': 3} |
| 4 | (3) T_fA_fT_f*-4A_f+3P_f | 1.171875e-02 | 3 | 8.2864e-03 | 8 | diagonal | {'q': 9}; {'q': 7} |
| 4 | (3) [X_f,T_fA_fT_f*] | 1.171875e-02 | 3 | 1.1719e-02 | 16 | dense-svd | {'q': 4}; {'q': 3} |
| 4 | (3) T_tA_tT_t*-4A_t+3P_t | 1.171875e-02 | 3 | 8.2864e-03 | 8 | diagonal | {'t': 9}; {'t': 7} |
| 4 | (3) [X_t,T_tA_tT_t*] | 1.171875e-02 | 3 | 1.1719e-02 | 16 | dense-svd | {'t': 4}; {'t': 3} |
| 4 | (4) guarded increment V | 5.524272e-03 | 1.41421 | 1.3811e-03 | 8 | dense-svd | {'x': 15, 'y': 3}; {'x': 15, 'y': 2} |
| 4 | (4) guarded increment U | 5.524272e-03 | 1.41421 | 1.3811e-03 | 2 | dense-svd | {'t': 15} |
| 4 | (6) V*A_aV-A_a+I-7/4H | 3.906250e-03 | 1 | 9.7656e-04 | 4 | diagonal | {'x': 15, 'y': 3}; {'x': 15, 'y': 2} |
| 4 | (24) [Y,VBV*]  (est. 32) | 4.577707e-05 | 0.0117189 | 2.2889e-05 | 16 | dense-svd | {'x': 13, 'y': 1}; {'x': 5, 'y': 1} |
| 6 | (3) T_aA_aT_a*-4A_a+3P_a | 7.324219e-04 | 3 | 5.1790e-04 | 256 | diagonal | {'x': 1, 'y': 4}; {'x': 1, 'y': 3} |
| 6 | (3) [X_a,T_aA_aT_a*] | 7.324219e-04 | 3 | 7.3242e-04 | 512 | dense-svd | {'x': 0, 'y': 4}; {'x': 0, 'y': 3} |
| 6 | (3) T_fA_fT_f*-4A_f+3P_f | 7.324219e-04 | 3 | 5.1790e-04 | 32 | diagonal | {'q': 9}; {'q': 7} |
| 6 | (3) [X_f,T_fA_fT_f*] | 7.324219e-04 | 3 | 7.3242e-04 | 64 | dense-svd | {'q': 4}; {'q': 3} |
| 6 | (3) T_tA_tT_t*-4A_t+3P_t | 7.324219e-04 | 3 | 5.1790e-04 | 32 | diagonal | {'t': 9}; {'t': 7} |
| 6 | (3) [X_t,T_tA_tT_t*] | 7.324219e-04 | 3 | 7.3242e-04 | 64 | dense-svd | {'t': 4}; {'t': 3} |
| 6 | (4) guarded increment V | 3.452670e-04 | 1.41421 | 4.3158e-05 | 16 | dense-svd | {'x': 63, 'y': 4}; {'x': 63, 'y': 3} |
| 6 | (4) guarded increment U | 3.452670e-04 | 1.41421 | 4.3158e-05 | 2 | dense-svd | {'t': 63} |
| 6 | (6) V*A_aV-A_a+I-7/4H | 2.441406e-04 | 1 | 3.0518e-05 | 8 | diagonal | {'x': 63, 'y': 4}; {'x': 63, 'y': 3} |
| 6 | (24) [Y,VBV*]  (est. 32) | 1.788139e-07 | 0.000732422 | 8.9407e-08 | 128 | dense-svd | {'x': 61, 'y': 1}; {'x': 61, 'y': 0} |
| 8 | (3) T_aA_aT_a*-4A_a+3P_a | 4.577637e-05 | 3 | 3.2369e-05 | 2048 | diagonal | {'x': 1, 'y': 4}; {'x': 1, 'y': 3} |
| 8 | (3) [X_a,T_aA_aT_a*] | 4.577637e-05 | 3 | 4.5776e-05 | 4096 | components(4096 | {'x': 0, 'y': 4}; {'x': 0, 'y': 3} |
| 8 | (3) T_fA_fT_f*-4A_f+3P_f | 4.577637e-05 | 3 | 3.2369e-05 | 128 | diagonal | {'q': 9}; {'q': 7} |
| 8 | (3) [X_f,T_fA_fT_f*] | 4.577637e-05 | 3 | 4.5776e-05 | 256 | dense-svd | {'q': 4}; {'q': 3} |
| 8 | (3) T_tA_tT_t*-4A_t+3P_t | 4.577637e-05 | 3 | 3.2369e-05 | 128 | diagonal | {'t': 9}; {'t': 7} |
| 8 | (3) [X_t,T_tA_tT_t*] | 4.577637e-05 | 3 | 4.5776e-05 | 256 | dense-svd | {'t': 4}; {'t': 3} |
| 8 | (4) guarded increment V | 2.157919e-05 | 1.41421 | 1.3487e-06 | 32 | dense-svd | {'x': 255, 'y': 4}; {'x': 255, 'y': 3} |
| 8 | (4) guarded increment U | 2.157919e-05 | 1.41421 | 1.3487e-06 | 2 | dense-svd | {'t': 255} |
| 8 | (6) V*A_aV-A_a+I-7/4H | 1.525879e-05 | 1 | 9.5367e-07 | 16 | diagonal | {'x': 255, 'y': 4}; {'x': 255, 'y': 3} |
| 8 | (24) [Y,VBV*]  (est. 32) | 1.788139e-07 | 0.0117188 | 3.9118e-08 | 1088 | dense-svd | {'x': 85, 'y': 4}; {'x': 85, 'y': 3} |
4 series {'B': {'states': 64, 'period': 16, 'exact_failures': 0, 'float_dev': 1.0449157878825003e-17}, 'C': {'states': 64, 'period': 16, 'exact_failures': 0, 'float_dev': 1.0449157878825003e-17}} positivity {'A (clock)': [0.0, 0.99609375], 'H': [0.0, 1.0], 'R': [0.0, 1.0], 'B': [0.0, 0.7529411764705882], 'C': [0.011764705882352941, 0.7529411764705882], 'r1': [0.0, 1.0], 's1': [0.0, 1.0], 'r2': [0.25, 1.0], 's2': [0.5, 1.0], 'r3': [0.0001220703125, 1.0], 's3': [0.000244140625, 1.0]}
4 fullspace mismatches [] 0.7534706592559814
6 series {'B': {'states': 512, 'period': 192, 'exact_failures': 0, 'float_dev': 1.0449157878825003e-17}, 'C': {'states': 512, 'period': 192, 'exact_failures': 0, 'float_dev': 1.0449157878825003e-17}} positivity {'A (clock)': [0.0, 0.999755859375], 'H': [0.0, 1.0], 'R': [0.0, 1.0], 'B': [0.0, 0.7529411764705882], 'C': [0.011764705882352941, 0.7529411764705882], 'r1': [0.0, 1.0], 's1': [0.0, 1.0], 'r2': [0.0009765625, 1.0], 's2': [0.001953125, 1.0], 'r3': [4.336808689942018e-19, 1.0], 's3': [8.673617379884035e-19, 1.0]}
6 fullspace mismatches [] 103.34725952148438
8 series {'B': {'states': 4096, 'period': 256, 'exact_failures': 0, 'float_dev': 4.179663151530001e-17}, 'C': {'states': 4096, 'period': 256, 'exact_failures': 0, 'float_dev': 4.179663151530001e-17}} positivity {'A (clock)': [0.0, 0.9999847412109375], 'H': [0.0, 1.0], 'R': [0.0, 1.0], 'B': [0.0, 0.9404411764705882], 'C': [0.011764705882352941, 0.9404411764705882], 'r1': [0.0, 1.0], 's1': [0.0, 1.0], 'r2': [3.552713678800501e-15, 1.0], 's2': [7.105427357601002e-15, 1.0], 'r3': [6.908934844075556e-77, 1.0], 's3': [1.3817869688151111e-76, 1.0]}
