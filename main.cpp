#include <fstream>
#include <iostream>
#include <string>
#include <math.h>
#include "stp/c_interface.h"
#include <assert.h>
using namespace std;

/* --------------------------------------------------------------------------------------------- */

/* Logic gate costs in 3 * 1.00GE */
#define NOT 2
#define XOR 9
#define XNOR 9
#define AND 4
#define NAND 3
#define OR 4
#define NOR 3
#define NAND3 4
#define AND3 5
#define NOR3 4
#define OR3 5
#define XNOR3 14
#define XOR3 14
#define MOAI1 6
#define MAOI1 8

/* B parameter type map */
#define B_8_NOT 3     // 0 0 0 0 0 0 1 1
#define B_8_XOR 4     // 0 0 0 0 0 1 0 0
#define B_8_XNOR 5    // 0 0 0 0 0 1 0 1
#define B_8_NOT2 7    // 0 0 0 0 0 1 1 1
#define B_8_AND 8     // 0 0 0 0 1 0 0 0
#define B_8_NAND 9    // 0 0 0 0 1 0 0 1
#define B_8_OR 12     // 0 0 0 0 1 1 0 0
#define B_8_NOR 13    // 0 0 0 0 1 1 0 1
#define B_8_AND3 64   // 0 1 0 0 0 0 0 0
#define B_8_NAND3 65  // 0 1 0 0 0 0 0 1
#define B_8_OR3 96    // 0 1 1 0 0 0 0 0
#define B_8_NOR3 97   // 0 1 1 0 0 0 0 1
#define B_8_XOR3 16   // 0 0 0 1 0 0 0 0
#define B_8_XNOR3 17  // 0 0 0 1 0 0 0 1
#define B_8_MAOI1 128 // 1 0 0 0 0 0 0 0
#define B_8_MOAI1 129 // 1 0 0 0 0 0 0 1

/* Other parameter */
#define N 3        // N-bit x N-bit S-box
#define Q_MAX 4    // Max inputs per gate, currently needs to be 4
#define NUMBER_B 8 // MIN 2

/* Variables */
int costs[16];
VC vc;

/* Structs */
struct SearchResult
{
    int K;
    double G;
};

/* --------------------------------------------------------------------------------------------- */

void InitializeCostsArray()
{
    costs[0] = NOT;
    costs[1] = XOR;
    costs[2] = XNOR;
    costs[3] = AND;
    costs[4] = NAND;
    costs[5] = OR;
    costs[6] = NOR;
    costs[7] = NAND3;
    costs[8] = AND3;
    costs[9] = NOR3;
    costs[10] = OR3;
    costs[11] = XNOR3;
    costs[12] = XOR3;
    costs[13] = MOAI1;
    costs[14] = MAOI1;
}

int Algorithm1(int K, int G, int *sbox, bool printAsserts = false, bool printVarDeclarations = false)
{

    int num_q = Q_MAX * K * pow(2, N);
    int num_t = K * pow(2, N);
    // int num_a = Q_MAX * (N + (N + K - 2)) * (K / 2) + N * N + N * K;
    // int num_a = pow(2, N) * (K * Q_MAX * (N + K / 2) - 1) + N * N + N * K;
    int num_a = (int)Q_MAX * (N + N + K - 1) * ((double)K / 2) // Number of connections between inputs and outputs of the logic gates and the s-box
                + N * N + N * K;                               // Number of connections betweens inputs and outputs of the s-box and the logic gates
    int num_b = NUMBER_B * K;

    int num_combinations = pow(2, N);

    // Bitvectors
    Expr x_bv[num_combinations * N], y_bv[num_combinations * N];
    Expr t_bv[num_t];
    Expr q_bv[num_q];
    Expr a_bv[num_a];
    Expr b_bv[num_b];
    Expr C_bv[K];
    Expr gec_bv;

    Expr zero = vc_bvConstExprFromInt(vc, 1, 0);
    Expr one = vc_bvConstExprFromInt(vc, 1, 1);
    Type type_bit = vc_bvType(vc, 1);

    /* --------------------------------------------------------------------------------------------- */
    /* Initialize vc variables */
    // x and y
    for (int i = 0; i < num_combinations * N; ++i)
    {
        string var_x_name = "x" + to_string(i);
        string var_y_name = "y" + to_string(i);
        x_bv[i] = vc_varExpr(vc, var_x_name.c_str(), type_bit);
        y_bv[i] = vc_varExpr(vc, var_y_name.c_str(), type_bit);
    }

    // t
    for (int i = 0; i < num_t; ++i)
    {
        string var_t_name = "t" + to_string(i);
        t_bv[i] = vc_varExpr(vc, var_t_name.c_str(), type_bit);
    }

    // q
    for (int i = 0; i < num_q; ++i)
    {
        string var_q_name = "q" + to_string(i);
        q_bv[i] = vc_varExpr(vc, var_q_name.c_str(), type_bit);
    }

    // a
    for (int i = 0; i < num_a; ++i)
    {
        string var_a_name = "a" + to_string(i);
        a_bv[i] = vc_varExpr(vc, var_a_name.c_str(), type_bit);
    }

    // b
    for (int i = 0; i < num_b; ++i)
    {
        string var_b_name = "b" + to_string(i);
        b_bv[i] = vc_varExpr(vc, var_b_name.c_str(), type_bit);
    }

    // C (costs)
    for (int i = 0; i < K; ++i)
    {
        string var_C_name = "C" + to_string(i);
        C_bv[i] = vc_varExpr(vc, var_C_name.c_str(), vc_bvType(vc, 8));
    }
    gec_bv = vc_varExpr(vc, "GEC", vc_bvType(vc, 8));

    /* --------------------------------------------------------------------------------------------- */
    /* Initialize vc S-box */
    for (int i = 0; i < num_combinations; ++i)
    {
        int x_n = i, y_n = sbox[i];

        Expr sx_expr[N], sy_expr[N], left, right, eq;

        left = x_bv[i * N];
        right = y_bv[i * N];

        for (int j = 1; j < N; ++j)
        {
            left = vc_bvConcatExpr(vc, left, x_bv[i * N + j]);
            right = vc_bvConcatExpr(vc, right, y_bv[i * N + j]);
        }

        left = vc_eqExpr(vc, left, vc_bvConstExprFromInt(vc, N, i));
        right = vc_eqExpr(vc, right, vc_bvConstExprFromInt(vc, N, sbox[i]));

        eq = vc_andExpr(vc, left, right);

        // Assert
        vc_assertFormula(vc, eq);
    }

    /* --------------------------------------------------------------------------------------------- */
    /* Restrictions */
    // Q_a - wires for gate inputs
    int a_start = 0, a_counter = N;
    for (int k = 0; k < K; ++k)
    {
        for (int q = 0; q < Q_MAX; ++q)
        {
            for (int i = a_start; i < a_start + a_counter - 1; ++i)
            {
                for (int j = i + 1; j < a_start + a_counter; ++j)
                {
                    Expr a_exp = vc_bvAndExpr(vc, a_bv[i], a_bv[j]);
                    Expr aeq_exp = vc_eqExpr(vc, a_exp, zero);
                    vc_assertFormula(vc, aeq_exp);
                }
            }
            a_start += a_counter;
        }
        a_counter++;
    }
    // Y_a - wires for outputs
    for (int k = 0; k < N; ++k)
    {
        for (int i = a_start; i < a_start + a_counter - 1; ++i)
        {
            for (int j = i + 1; j < a_start + a_counter; ++j)
            {
                Expr a_exp = vc_bvAndExpr(vc, a_bv[i], a_bv[j]);
                Expr aeq_exp = vc_eqExpr(vc, a_exp, zero);
                vc_assertFormula(vc, aeq_exp);
            }
        }
        a_start += a_counter;
    }

    // a = 0 or a = 1
    for (int i = 0; i < num_a; ++i)
    {
        Expr a_one = vc_eqExpr(vc, a_bv[i], one);
        Expr a_zero = vc_eqExpr(vc, a_bv[i], zero);
        Expr a_one_or_zero = vc_orExpr(vc, a_one, a_zero);
        vc_assertFormula(vc, a_one_or_zero);
    }

    // b = 0 or b = 1
    for (int i = 0; i < num_b; ++i)
    {
        Expr b_one = vc_eqExpr(vc, b_bv[i], one);
        Expr b_zero = vc_eqExpr(vc, b_bv[i], zero);
        Expr b_one_or_zero = vc_orExpr(vc, b_one, b_zero);
        vc_assertFormula(vc, b_one_or_zero);
    }

    // Constraints from table 6 and 7
    for (int k = 0; k < K; ++k)
    {
        int counter_b = k * NUMBER_B;
        // b6 = 1 => b7 = 1 and b4 = 0
        Expr cst1 = vc_iffExpr(vc, vc_eqExpr(vc, b_bv[counter_b + 6], one), vc_andExpr(vc, vc_eqExpr(vc, b_bv[counter_b + 7], one), vc_eqExpr(vc, b_bv[counter_b + 4], zero)));
        vc_assertFormula(vc, cst1);

        // b1 = 1 => b3 = b4 = b5 = b6 = 0
        Expr cst2 = vc_iffExpr(vc, vc_eqExpr(vc, b_bv[counter_b + 1], one), vc_andExpr(vc, vc_eqExpr(vc, b_bv[counter_b + 3], zero), vc_andExpr(vc, vc_eqExpr(vc, b_bv[counter_b + 4], zero), vc_andExpr(vc, vc_eqExpr(vc, b_bv[counter_b + 5], zero), vc_eqExpr(vc, b_bv[counter_b + 6], zero)))));
        vc_assertFormula(vc, cst2);

        // b2 = 1 => b1 = 1
        Expr cst3 = vc_iffExpr(vc, vc_eqExpr(vc, b_bv[counter_b + 2], one), vc_eqExpr(vc, b_bv[counter_b + 1], one));
        vc_assertFormula(vc, cst3);

        // b3 = 1 => b1 = b2 = b4 = b5 = b6 = 0
        Expr cst4 = vc_iffExpr(vc, vc_eqExpr(vc, b_bv[counter_b + 3], one), vc_andExpr(vc, vc_eqExpr(vc, b_bv[counter_b + 1], zero), vc_andExpr(vc, vc_eqExpr(vc, b_bv[counter_b + 2], zero), vc_andExpr(vc, vc_eqExpr(vc, b_bv[counter_b + 4], zero), vc_andExpr(vc, vc_eqExpr(vc, b_bv[counter_b + 5], zero), vc_eqExpr(vc, b_bv[counter_b + 6], zero))))));
        vc_assertFormula(vc, cst4);

        // b0 = 1 => b1 = b2 = b3 = b4 = b5 = b6 = 0
        Expr cst5 = vc_iffExpr(vc, vc_eqExpr(vc, b_bv[counter_b], one), vc_andExpr(vc, vc_eqExpr(vc, b_bv[counter_b + 1], zero), vc_andExpr(vc, vc_eqExpr(vc, b_bv[counter_b + 2], zero), vc_andExpr(vc, vc_eqExpr(vc, b_bv[counter_b + 3], zero), vc_andExpr(vc, vc_eqExpr(vc, b_bv[counter_b + 4], zero), vc_andExpr(vc, vc_eqExpr(vc, b_bv[counter_b + 5], zero), vc_eqExpr(vc, b_bv[counter_b + 6], zero)))))));
        vc_assertFormula(vc, cst5);
    }

    /* --------------------------------------------------------------------------------------------- */
    int counter_a = 0;
    for (int x = 0; x < num_combinations; ++x)
    {
        counter_a = 0;
        for (int k = 0; k < K; ++k)
        {
            // Gate inputs
            for (int q = 0; q < Q_MAX; ++q)
            {
                Expr q_xor_expr = zero;

                // One gate input is one of s-box inputs x
                for (int n = 0; n < N; ++n)
                {
                    Expr a_and_x = vc_bvAndExpr(vc, a_bv[counter_a], x_bv[x * N + n]);
                    q_xor_expr = vc_bvXorExpr(vc, q_xor_expr, a_and_x);

                    ++counter_a;
                }
                // or one of previous gate outputs t
                for (int t = 0; t < k; ++t)
                {
                    Expr a_and_t = vc_bvAndExpr(vc, a_bv[counter_a], t_bv[x * K + t]);
                    q_xor_expr = vc_bvXorExpr(vc, q_xor_expr, a_and_t);

                    ++counter_a;
                }

                Expr q_eq_expr = vc_eqExpr(vc, q_bv[x * K * Q_MAX + Q_MAX * k + q], q_xor_expr);
                vc_assertFormula(vc, q_eq_expr);
            }

#if Q_MAX == 4
            Expr t_xor_expr = zero;

            int counter_b = k * NUMBER_B;

            Expr bq1[] = {
                b_bv[counter_b],
                q_bv[x * K * Q_MAX + Q_MAX * k + 0],
                q_bv[x * K * Q_MAX + Q_MAX * k + 1],
                q_bv[x * K * Q_MAX + Q_MAX * k + 2],
                q_bv[x * K * Q_MAX + Q_MAX * k + 3]};
            t_xor_expr = vc_bvXorExpr(vc, t_xor_expr, vc_bvAndExpr(vc, bq1[0], vc_bvAndExpr(vc, bq1[1], vc_bvAndExpr(vc, bq1[2], vc_bvAndExpr(vc, bq1[3], bq1[4])))));

            Expr bq2[] = {
                b_bv[counter_b],
                q_bv[x * K * Q_MAX + Q_MAX * k + 0],
                q_bv[x * K * Q_MAX + Q_MAX * k + 1],
                q_bv[x * K * Q_MAX + Q_MAX * k + 2],
            };
            t_xor_expr = vc_bvXorExpr(vc, t_xor_expr, vc_bvAndExpr(vc, bq2[0], vc_bvAndExpr(vc, bq2[1], vc_bvAndExpr(vc, bq2[2], bq2[3]))));

            Expr bq3[] = {
                b_bv[counter_b],
                q_bv[x * K * Q_MAX + Q_MAX * k + 0],
                q_bv[x * K * Q_MAX + Q_MAX * k + 1],
                q_bv[x * K * Q_MAX + Q_MAX * k + 3],
            };
            t_xor_expr = vc_bvXorExpr(vc, t_xor_expr, vc_bvAndExpr(vc, bq3[0], vc_bvAndExpr(vc, bq3[1], vc_bvAndExpr(vc, bq3[2], bq3[3]))));

            Expr bq4[] = {
                b_bv[counter_b],
                q_bv[x * K * Q_MAX + Q_MAX * k + 2],
                q_bv[x * K * Q_MAX + Q_MAX * k + 3],
            };
            t_xor_expr = vc_bvXorExpr(vc, t_xor_expr, vc_bvAndExpr(vc, bq4[0], vc_bvAndExpr(vc, bq4[1], bq4[2])));

            Expr bq5[] = {
                b_bv[counter_b],
                q_bv[x * K * Q_MAX + Q_MAX * k + 2],
            };
            t_xor_expr = vc_bvXorExpr(vc, t_xor_expr, vc_bvAndExpr(vc, bq5[0], bq5[1]));

            Expr bq6[] = {
                b_bv[counter_b],
                q_bv[x * K * Q_MAX + Q_MAX * k + 3],
            };
            t_xor_expr = vc_bvXorExpr(vc, t_xor_expr, vc_bvAndExpr(vc, bq6[0], bq6[1]));

            Expr bq7[] = {
                b_bv[counter_b + 1],
                q_bv[x * K * Q_MAX + Q_MAX * k + 0],
                q_bv[x * K * Q_MAX + Q_MAX * k + 1],
                q_bv[x * K * Q_MAX + Q_MAX * k + 2],
            };
            t_xor_expr = vc_bvXorExpr(vc, t_xor_expr, vc_bvAndExpr(vc, bq7[0], vc_bvAndExpr(vc, bq7[1], vc_bvAndExpr(vc, bq7[2], bq7[3]))));

            Expr bq8[] = {
                b_bv[counter_b + 2],
                q_bv[x * K * Q_MAX + Q_MAX * k + 0],
                q_bv[x * K * Q_MAX + Q_MAX * k + 1],
            };
            t_xor_expr = vc_bvXorExpr(vc, t_xor_expr, vc_bvAndExpr(vc, bq8[0], vc_bvAndExpr(vc, bq8[1], bq8[2])));

            Expr bq9[] = {
                b_bv[counter_b + 2],
                q_bv[x * K * Q_MAX + Q_MAX * k + 0],
                q_bv[x * K * Q_MAX + Q_MAX * k + 2],
            };
            t_xor_expr = vc_bvXorExpr(vc, t_xor_expr, vc_bvAndExpr(vc, bq9[0], vc_bvAndExpr(vc, bq9[1], bq9[2])));

            Expr bq10[] = {
                b_bv[counter_b + 2],
                q_bv[x * K * Q_MAX + Q_MAX * k + 1],
                q_bv[x * K * Q_MAX + Q_MAX * k + 2],
            };
            t_xor_expr = vc_bvXorExpr(vc, t_xor_expr, vc_bvAndExpr(vc, bq10[0], vc_bvAndExpr(vc, bq10[1], bq10[2])));

            Expr bq11[] = {
                b_bv[counter_b + 2],
                q_bv[x * K * Q_MAX + Q_MAX * k + 0],
            };
            t_xor_expr = vc_bvXorExpr(vc, t_xor_expr, vc_bvAndExpr(vc, bq11[0], bq11[1]));

            Expr bq12[] = {
                b_bv[counter_b + 2],
                q_bv[x * K * Q_MAX + Q_MAX * k + 1],
            };
            t_xor_expr = vc_bvXorExpr(vc, t_xor_expr, vc_bvAndExpr(vc, bq12[0], bq12[1]));

            Expr bq13[] = {
                b_bv[counter_b + 2],
                q_bv[x * K * Q_MAX + Q_MAX * k + 2],
            };
            t_xor_expr = vc_bvXorExpr(vc, t_xor_expr, vc_bvAndExpr(vc, bq13[0], bq13[1]));

            Expr bq14[] = {
                b_bv[counter_b + 3],
                q_bv[x * K * Q_MAX + Q_MAX * k + 0],
            };
            t_xor_expr = vc_bvXorExpr(vc, t_xor_expr, vc_bvAndExpr(vc, bq14[0], bq14[1]));

            Expr bq15[] = {
                b_bv[counter_b + 3],
                q_bv[x * K * Q_MAX + Q_MAX * k + 1],
            };
            t_xor_expr = vc_bvXorExpr(vc, t_xor_expr, vc_bvAndExpr(vc, bq15[0], bq15[1]));

            Expr bq16[] = {
                b_bv[counter_b + 3],
                q_bv[x * K * Q_MAX + Q_MAX * k + 2],
            };
            t_xor_expr = vc_bvXorExpr(vc, t_xor_expr, vc_bvAndExpr(vc, bq16[0], bq16[1]));

            Expr bq17[] = {
                b_bv[counter_b + 4],
                q_bv[x * K * Q_MAX + Q_MAX * k + 0],
                q_bv[x * K * Q_MAX + Q_MAX * k + 1],
            };
            t_xor_expr = vc_bvXorExpr(vc, t_xor_expr, vc_bvAndExpr(vc, bq17[0], vc_bvAndExpr(vc, bq17[1], bq17[2])));

            Expr bq18[] = {
                b_bv[counter_b + 5],
                q_bv[x * K * Q_MAX + Q_MAX * k + 0],
            };
            t_xor_expr = vc_bvXorExpr(vc, t_xor_expr, vc_bvAndExpr(vc, bq18[0], bq18[1]));

            Expr bq19[] = {
                b_bv[counter_b + 5],
                q_bv[x * K * Q_MAX + Q_MAX * k + 1],
            };
            t_xor_expr = vc_bvXorExpr(vc, t_xor_expr, vc_bvAndExpr(vc, bq19[0], bq19[1]));

            Expr bq20[] = {
                b_bv[counter_b + 6],
                q_bv[x * K * Q_MAX + Q_MAX * k + 0],
            };
            t_xor_expr = vc_bvXorExpr(vc, t_xor_expr, vc_bvAndExpr(vc, bq20[0], bq20[1]));

            Expr bq21 = b_bv[counter_b + 7];
            t_xor_expr = vc_bvXorExpr(vc, t_xor_expr, bq21);

            Expr t_eq_expr = vc_eqExpr(vc, t_bv[x * K + k], t_xor_expr);

            vc_assertFormula(vc, t_eq_expr);

#endif
        }

        // Outputs y
        for (int y = 0; y < N; ++y)
        {
            Expr y_xor_expr = zero;

            // One output is one s-box input x
            for (int n = 0; n < N; ++n)
            {
                Expr a_and_x = vc_bvAndExpr(vc, a_bv[counter_a], x_bv[x * N + n]);
                y_xor_expr = vc_bvXorExpr(vc, y_xor_expr, a_and_x);

                ++counter_a;
            }
            // or one gate output t
            for (int t = 0; t < K; ++t)
            {
                Expr a_and_t = vc_bvAndExpr(vc, a_bv[counter_a], t_bv[x * K + t]);
                y_xor_expr = vc_bvXorExpr(vc, y_xor_expr, a_and_t);

                ++counter_a;
            }

            Expr y_eq_expr = vc_eqExpr(vc, y_bv[x * N + y], y_xor_expr);
            vc_assertFormula(vc, y_eq_expr);
        }
    }

    /* --------------------------------------------------------------------------------------------- */
    /* Costs */
    // Map combination of b to costs, sum it up and then check if lower than given gec
    for (int i = 0; i < K; ++i)
    {
        Expr b_conc;
        for (int j = NUMBER_B - 2; j >= 0; --j)
        {
            if (j == NUMBER_B - 2)
            {
                b_conc = vc_bvConcatExpr(vc, b_bv[i * NUMBER_B + j], b_bv[i * NUMBER_B + j + 1]);
            }
            else
            {
                b_conc = vc_bvConcatExpr(vc, b_bv[i * NUMBER_B + j], b_conc);
            }
        }

        vc_assertFormula(vc, vc_impliesExpr(vc, vc_eqExpr(vc, b_conc, vc_bvConstExprFromInt(vc, 8, B_8_NOT)), vc_eqExpr(vc, C_bv[i], vc_bvConstExprFromInt(vc, 8, NOT))));
        vc_assertFormula(vc, vc_impliesExpr(vc, vc_eqExpr(vc, b_conc, vc_bvConstExprFromInt(vc, 8, B_8_XOR)), vc_eqExpr(vc, C_bv[i], vc_bvConstExprFromInt(vc, 8, XOR))));
        vc_assertFormula(vc, vc_impliesExpr(vc, vc_eqExpr(vc, b_conc, vc_bvConstExprFromInt(vc, 8, B_8_XNOR)), vc_eqExpr(vc, C_bv[i], vc_bvConstExprFromInt(vc, 8, XNOR))));
        vc_assertFormula(vc, vc_impliesExpr(vc, vc_eqExpr(vc, b_conc, vc_bvConstExprFromInt(vc, 8, B_8_NOT2)), vc_eqExpr(vc, C_bv[i], vc_bvConstExprFromInt(vc, 8, NOT))));
        vc_assertFormula(vc, vc_impliesExpr(vc, vc_eqExpr(vc, b_conc, vc_bvConstExprFromInt(vc, 8, B_8_AND)), vc_eqExpr(vc, C_bv[i], vc_bvConstExprFromInt(vc, 8, AND))));
        vc_assertFormula(vc, vc_impliesExpr(vc, vc_eqExpr(vc, b_conc, vc_bvConstExprFromInt(vc, 8, B_8_NAND)), vc_eqExpr(vc, C_bv[i], vc_bvConstExprFromInt(vc, 8, NAND))));
        vc_assertFormula(vc, vc_impliesExpr(vc, vc_eqExpr(vc, b_conc, vc_bvConstExprFromInt(vc, 8, B_8_OR)), vc_eqExpr(vc, C_bv[i], vc_bvConstExprFromInt(vc, 8, OR))));
        vc_assertFormula(vc, vc_impliesExpr(vc, vc_eqExpr(vc, b_conc, vc_bvConstExprFromInt(vc, 8, B_8_NOR)), vc_eqExpr(vc, C_bv[i], vc_bvConstExprFromInt(vc, 8, NOR))));
        vc_assertFormula(vc, vc_impliesExpr(vc, vc_eqExpr(vc, b_conc, vc_bvConstExprFromInt(vc, 8, B_8_AND3)), vc_eqExpr(vc, C_bv[i], vc_bvConstExprFromInt(vc, 8, AND3))));
        vc_assertFormula(vc, vc_impliesExpr(vc, vc_eqExpr(vc, b_conc, vc_bvConstExprFromInt(vc, 8, B_8_NAND3)), vc_eqExpr(vc, C_bv[i], vc_bvConstExprFromInt(vc, 8, NAND3))));
        vc_assertFormula(vc, vc_impliesExpr(vc, vc_eqExpr(vc, b_conc, vc_bvConstExprFromInt(vc, 8, B_8_OR3)), vc_eqExpr(vc, C_bv[i], vc_bvConstExprFromInt(vc, 8, OR3))));
        vc_assertFormula(vc, vc_impliesExpr(vc, vc_eqExpr(vc, b_conc, vc_bvConstExprFromInt(vc, 8, B_8_NOR3)), vc_eqExpr(vc, C_bv[i], vc_bvConstExprFromInt(vc, 8, NOR3))));
        vc_assertFormula(vc, vc_impliesExpr(vc, vc_eqExpr(vc, b_conc, vc_bvConstExprFromInt(vc, 8, B_8_XOR3)), vc_eqExpr(vc, C_bv[i], vc_bvConstExprFromInt(vc, 8, XOR3))));
        vc_assertFormula(vc, vc_impliesExpr(vc, vc_eqExpr(vc, b_conc, vc_bvConstExprFromInt(vc, 8, B_8_XNOR3)), vc_eqExpr(vc, C_bv[i], vc_bvConstExprFromInt(vc, 8, XNOR3))));
        vc_assertFormula(vc, vc_impliesExpr(vc, vc_eqExpr(vc, b_conc, vc_bvConstExprFromInt(vc, 8, B_8_MAOI1)), vc_eqExpr(vc, C_bv[i], vc_bvConstExprFromInt(vc, 8, MAOI1))));
        vc_assertFormula(vc, vc_impliesExpr(vc, vc_eqExpr(vc, b_conc, vc_bvConstExprFromInt(vc, 8, B_8_MOAI1)), vc_eqExpr(vc, C_bv[i], vc_bvConstExprFromInt(vc, 8, MOAI1))));

        vc_assertFormula(vc, vc_eqExpr(vc, gec_bv, vc_bvPlusExprN(vc, 8, C_bv, K)));

        vc_assertFormula(vc, vc_bvLeExpr(vc, gec_bv, vc_bvConstExprFromInt(vc, 8, G)));
    }

    if (printVarDeclarations)
    {
        vc_printVarDecls(vc);
    }

    if (printAsserts)
    {
        vc_printAsserts(vc);
    }

    int result = vc_query(vc, vc_falseExpr(vc));

    vc_printCounterExample(vc);

    return result;
}

SearchResult Algorithm2(int K_low, int G_up, int *sbox)
{
    int K_up = G_up;
    int G_low = K_low;

    int K_opt = K_low;
    int G_opt = G_up;

    for (int K = K_low; K <= ((double)K_up / 3); ++K)
    {
        for (int G = G_up; G >= G_low; --G)
        {
            cout << "Call Algorithm1 for K = " << K << " and G = " << (double)G / 3 << "..." << endl;
            if (Algorithm1(K, G, sbox) == 0)
            {
                G_up = G;
                K_up = G;

                G_opt = G;
                K_opt = K;
            }
            else
            {

                break;
            }
        }
    }

    SearchResult result = {K_opt,
                           (double)G_opt / 3.00};

    return result;
}

int main()
{
    // Create stp validity checker
    vc = vc_createValidityChecker();
    // vc_setFlags(vc, 'n');
    // vc_setFlags(vc, 'd');
    // vc_setFlags(vc, 'p');

    InitializeCostsArray();

    // int sbox[N * N] = {2, 3, 3, 1};                      // 2x2
    // int res = Algorithm1(2, 7, sbox, false, false);
    // SearchResult result = Algorithm2(2, 7, sbox);
    // cout << "K_opt: " << result.K << endl;
    // cout << "G_opt: " << result.G << endl;


    int sbox[N * N] = {7, 4, 3, 2, 0, 1, 5, 6};          // 3x3
    int K = 6, G = 17;
    // int res = Algorithm1(K, 3 * G, sbox, false, false);
    SearchResult result = Algorithm2(K, 3 * G, sbox);
    cout << "K_opt: " << result.K << endl;
    cout << "G_opt: " << result.G << endl;

    // Delete validity checker
    vc_Destroy(vc);

    return 0;
}