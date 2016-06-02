package org.jacop;

import org.jacop.fz.Fz2jacop;
import org.junit.BeforeClass;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.IOException;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;

import static org.junit.Assert.assertEquals;

/**
 * @author Mariusz Świerkot
 */

@RunWith(Parameterized.class)
public class MinizincBasedTest {
    private String inputString;
    private static Fz2jacop fz2jacop;
    private static final String relativePath = "src/test/fz/";
    private static final boolean printInfo = true;

    @BeforeClass
    public static void initialize() {
        fz2jacop = new Fz2jacop();
    }


    public MinizincBasedTest(String inputString) {
        this.inputString = inputString;

    }

    @Parameterized.Parameters
    public static Collection parametricTest() {


        return Arrays.asList(new Object[][]{
/*
               //costasArray
               {"upTo1min/costasArray/CostasArrayTestN16"},
               {"upTo10min/costasArray/CostasArrayTestN17"},
               {"upTo30sec/costasArray/CostasArrayTestN18"},
               {"above1hour/costasArray/CostasArrayTestN19"},
               {"above1hour/costasArray/CostasArrayTestN20"},

               //cvrp
               {"upTo1min/cvrp/simple2"},

               //freepizza
               {"upTo1hour/freepizza/pizza6"},


               //grid-colouring
               {"upTo5sec/grid-colouring/4_8"},
               {"upTo1min/grid-colouring/10_5"},

               //is
               {"upTo5min/is/A3PZaPjnUz"},
               {"upTo30sec/is/jZ9pQqRxJ2"},

               //multi-knapsack
               {"upTo5sec/multi-knapsack/mknap1-6"},
               {"upTo5sec/multi-knapsack/mknap2-1"},
               {"upTo10min/multi-knapsack/mknap2-2"},
               {"upTo5sec/multi-knapsack/mknap2-20"},
               {"upTo5sec/multi-knapsack/mknap2-32"},

               //nmseq
               {"upTo5sec/nmseq/83"},
               {"upTo5min/nmseq/176"},
               {"upTo10min/nmseq/207"},
               {"upTo1hour/nmseq/269"},
               {"above1hour/nmseq/393"},

               //opd
               {"upTo1hour/opd/small_bibd_10_30_09"},
               {"upTo1hour/opd/small_bibd_11_22_10"},
               {"upTo1hour/opd/small_bibd_13_26_06"},

               //open_stacks
               {"upTo30sec/open_stacks/problem_30_15_1"},
               {"upTo1hour/open_stacks/wbp_20_20_1"},
               {"upTo5min/open_stacks/wbo_10_20_1"},
               {"upTo1hour/open_stacks/problem_20_20_1"},

               //p1f
               {"upTo5sec/p1f/13"},
               {"upTo30sec/p1f/15"},
               {"upTo10min/p1f/17"},

               //radiation
               {"upTo10min/radiation/i6-11"},
               {"upTo30sec/radiation/i7-9"},
               {"upTo1hour/radiation/i9-11"},
               {"upTo10min/radiation/i6-21"},

               //roster
               {"upTo5sec/roster/chicroster_dataset_2"},
               {"upTo5sec/roster/chicroster_dataset_5"},
               {"upTo5sec/roster/chicroster_dataset_7"},
               {"upTo5sec/roster/chicroster_dataset_11"},
               {"upTo5sec/roster/chicroster_dataset_17"},

               //tdtsp
               {"upTo1hour/tdtsp/inst_10_24_10"},
               {"upTo1hour/tdtsp/inst_10_34_00"},
               {"above1hour/tdtsp/inst_10_42_10"},

               //arbitrage_loops
               {"upTo5sec/arbitrage_loops/arbitrage_loops1"},
               {"upTo5sec/arbitrage_loops/arbitrage_loops2"},
               {"upTo5sec/arbitrage_loops/arbitrage_loops3"},
               {"upTo5sec/arbitrage_loops/arbitrage_loops4"},
               {"upTo5min/arbitrage_loops/arbitrage_loops5"},

               //carpool_fairness1
               {"upTo5sec/carpool_fairness/carpool_fairness"},
               {"upTo5sec/carpool_fairness/carpool_fairness1"},
               {"upTo5sec/carpool_fairness/carpool_fairness2"},
               {"upTo5sec/carpool_fairness/carpool_fairness3"},
               {"upTo5sec/carpool_fairness/carpool_fairness4"},
               {"upTo5sec/carpool_fairness/carpool_fairness5"},

               //domino
               {"upTo5sec/domino/domino0"},
               {"upTo5sec/domino/domino1"},
               {"upTo5sec/domino/domino2"},
               {"upTo5sec/domino/domino3"},
               {"upTo5sec/domino/domino4"},
               {"upTo5sec/domino/domino5"},

               //fill_a_pix
               {"upTo5sec/fill_a_pix/fill_a_pix1"},
               {"upTo5sec/fill_a_pix/fill_a_pix2"},
               {"upTo5sec/fill_a_pix/fill_a_pix3"},

               //strimko
               {"upTo5sec/strimko/strimko_002"},
               {"upTo5sec/strimko/strimko_067"},
               {"upTo5sec/strimko/strimko_068"},
               {"upTo5sec/strimko/strimko_070"},

               //strimko2
               {"upTo5sec/strimko2/strimko2_002"},
               {"upTo5sec/strimko2/strimko2_067"},
               {"upTo5sec/strimko2/strimko2_068"},
               {"upTo5sec/strimko2/strimko2_070"},

               //letter_square
               {"upTo5sec/letter_square/letter_square1"},
               {"upTo5sec/letter_square/letter_square59"},
               {"upTo5sec/letter_square/letter_square60"},
               {"upTo5sec/letter_square/letter_square89"},

               //monorail
               {"upTo5sec/monorail/monorail1"},
               {"upTo5sec/monorail/monorail2"},

               //3_coins
               {"upTo5sec/3_coins/3_coins"},

               //1d_rubiks_cube
               {"upTo5sec/1d_rubiks_cube/1d_rubiks_cube"},

               //3_jugs2
               {"upTo5sec/3_jugs2/3_jugs2"},

               //3_jugs2_all
               {"upTo5sec/3_jugs2_all/3_jugs2_all"},

               //3sum
               {"upTo5sec/3sum/3sum"},

               //5x5_puzzle
               {"upTo5sec/5x5_puzzle/5x5_puzzle"},

               //17_b
               {"upTo5sec/17_b/17_b"},

               //18_hole_golf
               {"upTo5sec/18_hole_golf/18_hole_golf"},

               //50_puzzle/50_puzzle
               {"upTo5sec/50_puzzle/50_puzzle"},

               //99_bottles_of_beer
               {"upTo5sec/99_bottles_of_beer/99_bottles_of_beer"}, //??????????????????????????

               //a_league_of_their_own_enigma_1217
               {"upTo5sec/a_league_of_their_own_enigma_1217/a_league_of_their_own_enigma_1217"},

               //a_puzzle
               {"upTo5sec/a_puzzle/a_puzzle"},

               //a_round_of_golf
               {"upTo5sec/a_round_of_golf/a_round_of_golf"},

               //abbots_puzzle
               {"upTo5sec/abbots_puzzle/abbots_puzzle"},

               //abbott
               {"upTo5sec/abbott/abbott"},

               //abc_endview
               {"upTo5sec/abc_endview/abc_endview"},

               //abpuzzle
               {"upTo5sec/abpuzzle/abpuzzle"},

               //added_corner
               {"upTo5sec/added_corner/added_corner"},

               //adjacency_matrix_from_degrees
               {"upTo5sec/adjacency_matrix_from_degrees/adjacency_matrix_from_degrees"},

               //age_changing
               {"upTo5sec/age_changing/age_changing"},

               //ages2
               {"upTo5sec/ages2/ages2"},

               //all_differ_from_at_least_k_pos
               {"upTo5sec/all_differ_from_at_least_k_pos/all_differ_from_at_least_k_pos"},

               //all_equal_me
               {"upTo5sec/all_equal_me/all_equal_me"},

               //all_interval
               {"upTo30sec/all_interval/all_interval"},

               //all_interval1
               {"upTo5sec/all_interval1/all_interval1"},

               //all_interval2
               {"upTo5sec/all_interval2/all_interval2"},

               //all_interval3
               {"upTo5sec/all_interval3/all_interval3"},

               //all_interval4
               {"upTo5sec/all_interval4/all_interval4"},

               //all_interval5
               {"upTo5sec/all_interval5/all_interval5"},

               //all_interval6
               {"upTo5sec/all_interval6/all_interval6"},

               //all_min_dist
               {"upTo5sec/all_min_dist/all_min_dist"},

               //all_paths_graph
               {"upTo5sec/all_paths_graph/all_paths_graph"},

               //alldifferent_consecutive_values
               {"upTo5sec/alldifferent_consecutive_values/alldifferent_consecutive_values"},

               //alldifferent_cst
               {"upTo5sec/alldifferent_cst/alldifferent_cst"},

               //alldifferent_except_0_me
               {"upTo5sec/alldifferent_except_0_me/alldifferent_except_0_me"},

               //alldifferent_explain
               {"upTo5sec/alldifferent_explain/alldifferent_explain"},

               //alldifferent_interval
               {"upTo5sec/alldifferent_interval/alldifferent_interval"},

               //alldifferent_modulo
               {"upTo5sec/alldifferent_modulo/alldifferent_modulo"},

               //alldifferent_on_intersection
               {"upTo5sec/alldifferent_on_intersection/alldifferent_on_intersection"},

               //alldifferent_pairs
               {"upTo5sec/alldifferent_pairs/alldifferent_pairs"},

               //alldifferent_partition
               {"upTo5sec/alldifferent_partition/alldifferent_partition"},

               //alldifferent_same_value
               {"upTo5sec/alldifferent_same_value/alldifferent_same_value"},

               //alldifferent_soft
               {"upTo5sec/alldifferent_soft/alldifferent_soft"},

               //allocating_developments
               {"upTo5sec/allocating_developments/allocating_developments"},

               //allperm
               {"upTo5sec/allperm/allperm"},

               //among_diff_0
               {"upTo5sec/among_diff_0/among_diff_0"},

               //among_interval
               {"upTo5sec/among_interval/among_interval"},

               //among_modulo
               {"upTo5sec/among_modulo/among_modulo"},

               //among_seq
               {"upTo5sec/among_seq/among_seq"},

               //and
               {"upTo5sec/and/and"},

               //anniversaries
               {"upTo5sec/anniversaries/anniversaries"},

               //another_kind_of_magic_square
               {"upTo5sec/another_kind_of_magic_square/another_kind_of_magic_square"},

               //antisymmetric
               {"upTo5sec/antisymmetric/antisymmetric"},

               //ppointment_scheduling_set
               {"upTo5sec/appointment_scheduling_set/appointment_scheduling_set"},

               //arch_friends
               {"upTo5sec/arch_friends/arch_friends"},

               //archery_puzzle
               {"upTo5sec/archery_puzzle/archery_puzzle"},

               //argmax
               {"upTo5sec/argmax/argmax"},

               //arith_or
               {"upTo5sec/arith_or/arith_or"},

               //arith_sliding
               {"upTo5sec/arith_sliding/arith_sliding"},

               //assign_and_counts
               {"upTo5sec/assign_and_counts/assign_and_counts"},

               //assign_and_nvalues
               {"upTo5sec/assign_and_nvalues/assign_and_nvalues"},

               //assignment
               {"upTo5sec/assignment/assignment"},

               //assignment2
               {"upTo5sec/assignment2/assignment2"},

               //assignment2_2
               {"upTo5sec/assignment2_2/assignment2_2"},

               //assignment3
               {"upTo5sec/assignment3/assignment3"},

               //assignment5
               {"upTo5sec/assignment5/assignment5"},

               //assignment6
               {"upTo5sec/assignment6/assignment6"},

               //atleast_nvalue
               {"upTo5sec/atleast_nvalue/atleast_nvalue"},

               //atmost1_me
               {"upTo5sec/atmost1_me/atmost1_me"},

               //atmost_nvalue
               {"upTo5sec/atmost_nvalue/atmost_nvalue"},

               //atom_smasher
               {"upTo5sec/atom_smasher/atom_smasher"},

               //average_avoiding
               {"upTo5sec/average_avoiding/average_avoiding"},

               //averbach_1.2
               {"upTo5sec/averbach_1.2/averbach_1.2"},

               //averbach_1.3
               {"upTo5sec/averbach_1.3/averbach_1.3"},

               //averbach_1.4
               {"upTo5sec/averbach_1.4/averbach_1.4"},

               //averbach_1.5
               {"upTo5sec/averbach_1.5/averbach_1.5"},

               //babysitting
               {"upTo5sec/babysitting/babysitting"},


               //balance_interval
               {"upTo5sec/balance_interval/balance_interval"},

               //balance_modulo
               {"upTo5sec/balance_modulo/balance_modulo"},

               //balance_partition
               {"upTo5sec/balance_partition/balance_partition"},

               //balanced_brackets
               {"upTo5sec/balanced_brackets/balanced_brackets"},

               //balanced_matrix
               {"upTo5sec/balanced_matrix/balanced_matrix"},

               //bales_of_hay
               {"upTo5sec/bales_of_hay/bales_of_hay"},

               //bananas
               {"upTo5sec/bananas/bananas"},

               //bank_card
               {"upTo5sec/bank_card/bank_card"},

               //barrels
               {"upTo5sec/barrels/barrels"},

               //before_and_after
               {"upTo5sec/before_and_after/before_and_after"},

               //bertrand_russell_puzzle
               {"upTo5sec/bertrand_russell_puzzle/bertrand_russell_puzzle"},

               //best_host
               {"upTo5sec/best_host/best_host"},

               //best_shuffle
               {"upTo5sec/best_shuffle/best_shuffle"},

               //between_min_max
               {"upTo5sec/between_min_max/between_min_max"},

               //bin_packing2
               {"upTo5sec/bin_packing2/bin_packing2"},

               //binary_matrix2array
               {"upTo5sec/binary_matrix2array/binary_matrix2array"},

               //binary_puzzle
               {"upTo5sec/binary_puzzle/binary_puzzle"},

               //binary_sudoku
               {"upTo5sec/binary_sudoku/binary_sudoku"},

               //binary_tree
               {"upTo5sec/binary_tree/binary_tree"},

               //binero
               {"upTo5sec/binero/binero"},

               //bipartite
               {"upTo5sec/bipartite/bipartite"},

               //birthday_paradox
               {"upTo5sec/birthday_paradox/birthday_paradox"},

               //birthdays_2010
               {"upTo5sec/birthdays_2010/birthdays_2010"},

               //bit_vector1
               {"upTo5sec/bit_vector1/bit_vector1"},

               //blending_problem
               {"upTo5sec/blending_problem/blending_problem"},

               //blueberry_muffins
               {"upTo5sec/blueberry_muffins/blueberry_muffins"},

               //book_buy
               {"upTo5sec/book_buy/book_buy"},

               //book_discount
               {"upTo5sec/book_discount/book_discount"},

               //box
               {"upTo5sec/box/box"},

               //bpp
               {"upTo5sec/bpp/bpp"},

               //bratko_scheduling
               {"upTo5sec/bratko_scheduling/bratko_scheduling"},

               //bratko_scheduling2
               {"upTo5sec/bratko_scheduling2/bratko_scheduling2"},

               //bridges_to_somewhere
               {"upTo5sec/bridges_to_somewhere/bridges_to_somewhere"},

               //broken_weights
               {"upTo5sec/broken_weights/broken_weights"},

               //buckets
               {"upTo5sec/buckets/buckets"},//costasArray
                {"upTo1min/costasArray/CostasArrayTestN16"},
                {"upTo10min/costasArray/CostasArrayTestN17"},
                {"upTo30sec/costasArray/CostasArrayTestN18"},
                {"above1hour/costasArray/CostasArrayTestN19"},
                {"above1hour/costasArray/CostasArrayTestN20"},


               //building_a_house2
               {"upTo5sec/building_a_house2/building_a_house2"},

               //calculs_d_enfer
               {"upTo5sec/calculs_d_enfer/calculs_d_enfer"},

               //calvin_puzzle
               {"upTo5sec/calvin_puzzle/calvin_puzzle"},

               //capital_budget2
               {"upTo5sec/capital_budget2/capital_budget2"},

               //car
               {"upTo5sec/car/car"},

               //car_painting
               {"upTo5sec/car_painting/car_painting"},

               //car_talk_odometer
               {"upTo5sec/car_talk_odometer/car_talk_odometer"},

               //cardinality_atleast
               {"upTo5sec/cardinality_atleast/cardinality_atleast"},

               //cardinality_atmost
               {"upTo5sec/cardinality_atmost/cardinality_atmost"},

               //cardinality_atmost_partition
               {"upTo5sec/cardinality_atmost_partition/cardinality_atmost_partition"},

               //cashier_change
               {"upTo5sec/cashier_change/cashier_change"},

               //catalan_numbers
               {"upTo5sec/catalan_numbers/catalan_numbers"},

               //celsius_fahrenheit
               {"upTo5sec/celsius_fahrenheit/celsius_fahrenheit"},

               //chain_of_primes
               {"upTo5sec/chain_of_primes/chain_of_primes"},

               //chandelier_balancing
               {"upTo5sec/chandelier_balancing/chandelier_balancing"},

               //1d_rubiks_cube2
               {"upTo30sec/1d_rubiks_cube2/1d_rubiks_cube2"},

               //krypto
               {"upTo5sec/krypto/krypto"},

               //labeled_dice
               {"upTo5sec/labeled_dice/labeled_dice"},

               //lager
               {"upTo5sec/lager/lager"},

               //change
               {"upTo5sec/change/change"},

               //change_pair
               {"upTo5sec/change_pair/change_pair"},

               //change_partition
               {"upTo5sec/change_partition/change_partition"},

               //checker_puzzle
               {"upTo5sec/checker_puzzle/checker_puzzle"},

               //chessset
               {"upTo5sec/chessset/chessset"},

               //chinese_remainder_problem
               {"upTo5sec/chinese_remainder_problem/chinese_remainder_problem"},

               //choose_your_crew
               {"upTo5sec/choose_your_crew/choose_your_crew"},

               //choosing_teams
               {"upTo5sec/choosing_teams/choosing_teams"},

               //choosing_teams2
               {"upTo5sec/choosing_teams2/choosing_teams2"},

               //circle_intersection
               {"upTo5sec/circle_intersection/circle_intersection"},

               //circling_squares
               {"upTo5sec/circling_squares/circling_squares"},

               //circuit_path
               {"upTo5sec/circuit_path/circuit_path"},

               //circuit_test
               {"upTo5sec/circuit_test/circuit_test"},

               //circular_change
               {"upTo5sec/circular_change/circular_change"},

               //col_sum_puzzle
               {"upTo5sec/col_sum_puzzle/col_sum_puzzle"},

               //collatz
               {"upTo5sec/collatz/collatz"},

               //color
               {"upTo5sec/color/color"},

               //color_simple
               {"upTo5sec/color_simple/color_simple"},

               //coloring_ip
               {"upTo5sec/coloring_ip/coloring_ip"},

               //combination_locks
               {"upTo5sec/combination_locks/combination_locks"},

               //combinatorial_auction
               {"upTo5sec/combinatorial_auction/combinatorial_auction"},

               //common
               {"upTo5sec/common/common"},

               //common_interval
               {"upTo5sec/common_interval/common_interval"},

               //common_modulo
               {"upTo5sec/common_modulo/common_modulo"},

               //common_partition
               {"upTo5sec/common_partition/common_partition"},

               //building_a_house
               {"upTo30sec/building_a_house/building_a_house"},

               //clique
               {"upTo5sec/clique/clique"},

               //clock_triplets
               {"upTo5sec/clock_triplets/clock_triplets"},

               //coins3
               {"upTo5sec/coins3/coins3"},

               //coins3b
               {"upTo5sec/coins3b/coins3b"},

               //coins_41_58
               {"upTo5sec/coins_41_58/coins_41_58"},

               //cond_lex_less
               {"upTo5sec/cond_lex_less/cond_lex_less"},

               //conference
               {"upTo5sec/conference/conference"},

               //config
               {"upTo5sec/config/config"},

               //congress
               {"upTo5sec/congress/congress"},

               //contiguity_mip
               {"upTo5sec/contiguity_mip/contiguity_mip"},

               //contiguity_regular
               {"upTo5sec/contiguity_regular/contiguity_regular"},

               //contractor_costs
               {"upTo5sec/contractor_costs/contractor_costs"},

               //cookie_bake_off.out
               {"upTo5sec/cookie_bake_off/cookie_bake_off"},

               //cookie_monster_problem
               {"upTo5sec/cookie_monster_problem/cookie_monster_problem"},

               //copy_arrays
               {"upTo5sec/copy_arrays/copy_arrays"},

               //copy_arrays2.out
               {"upTo5sec/copy_arrays2/copy_arrays2"},

               //correspondence
               {"upTo5sec/correspondence/correspondence"},

               //costas_array
               {"upTo5sec/costas_array/costas_array"},

               //count_ctr
               {"upTo5sec/count_ctr/count_ctr"},

               //countdown
               {"upTo5sec/countdown/countdown"},

               //counts
               {"upTo5sec/counts/counts"},

               //critical_path1
               {"upTo5sec/critical_path1/critical_path1"},

               //crossbar
               {"upTo5sec/crossbar/crossbar"},

               //crossfigure
               {"upTo5sec/crossfigure/crossfigure"},

               //crossword
               {"upTo5sec/crossword/crossword"},

               //crossword2
               {"upTo5sec/crossword2/crossword2"},

               //crossword_bratko
               {"upTo5sec/crossword_bratko/crossword_bratko"},

               //crypta
               {"upTo5sec/crypta/crypta"},

               //crypto
               {"upTo5sec/crypto/crypto"},

               //cutting_stock_winston
               {"upTo5sec/cutting_stock_winston/cutting_stock_winston"},

               //cycle_test2
               {"upTo5sec/cycle_test2/cycle_test2"},

               //cycle_test3
               {"upTo5sec/cycle_test3/cycle_test3"},

               //cyclohexane
               {"upTo5sec/cyclohexane/cyclohexane"},

               //dakota_furniture
               {"upTo5sec/dakota_furniture/dakota_furniture"},

               //debruijn2d
               {"upTo5sec/debruijn2d/debruijn2d"},

               //debruijn_binary
               {"upTo5sec/debruijn_binary/debruijn_binary"},

               //decision_tree_binary
               {"upTo5sec/decision_tree_binary/decision_tree_binary"},

               //decreasing_me
               {"upTo5sec/decreasing_me/decreasing_me"},

               //defending_castle
               {"upTo5sec/defending_castle/defending_castle"},

               //dennys_menu
               {"upTo5sec/dennys_menu/dennys_menu"},

               //derangement
               {"upTo5sec/derangement/derangement"},

               //devils_word
               {"upTo5sec/devils_word/devils_word"},

               //dice_with_a_difference_enigma_290
               {"upTo5sec/dice_with_a_difference_enigma_290/dice_with_a_difference_enigma_290"},

               //differs_from_at_least_k_pos
               {"upTo5sec/differs_from_at_least_k_pos/differs_from_at_least_k_pos"},

               //diffn_me
               {"upTo5sec/diffn_me/diffn_me"}, //Warning: Not implemented indomain method "indomain"; used indomain_min

               //digital_roots
               {"upTo5sec/digital_roots/digital_roots"},

               //dimes
               {"upTo5sec/dimes/dimes"},

               //dinner
               {"upTo5sec/dinner/dinner"},

               //discrepancy
               {"upTo5sec/discrepancy/discrepancy"},

               //discrete_tomography
               {"upTo5sec/discrete_tomography/discrete_tomography"},

               //disjunctive
               {"upTo5sec/disjunctive/disjunctive"},

               //distance_between
               {"upTo5sec/distance_between/distance_between"},

               //distance_change
               {"upTo5sec/distance_change/distance_change"},

               //dividing_the_spoils
               {"upTo5sec/dividing_the_spoils/dividing_the_spoils"},

               //divisible_by_7
               {"upTo5sec/divisible_by_7/divisible_by_7"},

               //divisors_ending_in_0_to_9
               {"upTo5sec/divisors_ending_in_0_to_9/divisors_ending_in_0_to_9"},

               //domain
               {"upTo5sec/domain/domain"},

               //domain_constraint
               {"upTo5sec/domain_constraint/domain_constraint"},

               //donald
               {"upTo5sec/donald/donald"},

               //donald3
               {"upTo5sec/donald2/donald2"},

               //drinking_game
               {"upTo5sec/drinking_game/drinking_game"},

               //drive_ya_nuts
               {"upTo5sec/drive_ya_nuts/drive_ya_nuts"},

               //dudeney_bishop_placement2
               {"upTo30sec/dudeney_bishop_placement2/dudeney_bishop_placement2"},

               //dudeney_numbers
               {"upTo5sec/dudeney_numbers/dudeney_numbers"},

               //earthlin
               {"upTo5sec/earthlin/earthlin"},

               //egg_basket
               {"upTo5sec/egg_basket/egg_basket"},

               //ein_ein_ein_ein_vier
               {"upTo5sec/ein_ein_ein_ein_vier/ein_ein_ein_ein_vier"},

               //einav_puzzle
               {"upTo5sec/einav_puzzle/einav_puzzle"},

               //einstein_hurlimann
               {"upTo5sec/einstein_hurlimann/einstein_hurlimann"},

               //einstein_opl
               {"upTo5sec/einstein_opl/einstein_opl"},

               //element_greatereq
               {"upTo5sec/element_greatereq/element_greatereq"},

               //element_lesseq
               {"upTo5sec/element_lesseq/element_lesseq"},

               //element_matrix
               {"upTo5sec/element_matrix/element_matrix"},

               //element_product
               {"upTo5sec/element_product/element_product"},

               //element_sparse
               {"upTo5sec/element_sparse/element_sparse"},

               //elementn
               {"upTo5sec/elementn/elementn"},

               //elements
               {"upTo5sec/elements/elements"},

               //elements_alldifferent
               {"upTo5sec/elements_alldifferent/elements_alldifferent"},

               //elevator_6_3
               {"upTo5sec/elevator_6_3/elevator_6_3"},

               //elevator_8_4
               {"upTo30sec/elevator_8_4/elevator_8_4"},

               //eliza_pseudonym7
               {"upTo5sec/eliza_pseudonym7/eliza_pseudonym7"},

               //enclosed_tiles
               {"upTo5sec/enclosed_tiles/enclosed_tiles"},

               //enigma
               {"upTo5sec/enigma/enigma"},

               //enigma2
               {"upTo5sec/enigma2/enigma2"},

               //enigma_95_for_love_and_money
               {"upTo30sec/enigma_95_for_love_and_money/enigma_95_for_love_and_money"},

               //enigma_248_add_or_multiply
               {"upTo5sec/enigma_248_add_or_multiply/enigma_248_add_or_multiply"},

               //enigma_843
               {"upTo5sec/enigma_843/enigma_843"},

               //enigma_1000
               {"upTo5sec/enigma_1000/enigma_1000"},

               //enigma_1001
               {"upTo5sec/enigma_1001/enigma_1001"},

               //enigma_1266_unhelpful_square
               {"upTo5sec/enigma_1266_unhelpful_square/enigma_1266_unhelpful_square"},

               //enigma_1293
               {"upTo5sec/enigma_1293/enigma_1293"},

               //enigma_1530
               {"upTo5sec/enigma_1530/enigma_1530"},

               //enigma_1535
               {"upTo5sec/enigma_1535/enigma_1535"},

               //enigma_1553
               {"upTo5sec/enigma_1553/enigma_1553"},

               //enigma_1555
               {"upTo5sec/enigma_1555/enigma_1555"},

               //enigma_1568
               {"upTo5sec/enigma_1568/enigma_1568"},

               //enigma_1573
               {"upTo5sec/enigma_1573/enigma_1573"},

               //enigma_1576
               {"upTo5sec/enigma_1576/enigma_1576"},

               //enigma_1577
               {"upTo5sec/enigma_1577/enigma_1577"},

               //enigma_1615
               {"upTo5sec/enigma_1615/enigma_1615"},

               //enigma_1631
               {"upTo30sec/enigma_1631/enigma_1631"},

               //enigma_birthday_magic
               {"upTo5sec/enigma_birthday_magic/enigma_birthday_magic"},

               //enigma_circular_chain
               {"upTo5sec/enigma_circular_chain/enigma_circular_chain"},

               //enigma_counting_pennies
               {"upTo5sec/enigma_counting_pennies/enigma_counting_pennies"},

               //enigma_eight_times
               {"upTo5sec/enigma_eight_times/enigma_eight_times"}, //Warning: Not implemented indomain method "indomain"; used indomain_min

               {"upTo5sec/enigma_eight_times2/enigma_eight_times2"}, //Warning: Not implemented indomain method "indomain"; used indomain_min

               //enigma_five_fives
               {"upTo5sec/enigma_five_fives/enigma_five_fives"},

               //enigma_planets
               {"upTo5sec/enigma_planets/enigma_planets"},

               //equation
               {"upTo5sec/equation/equation"},

               //equivalent
               {"upTo5sec/equivalent/equivalent"},

               //ett_ett_ett_ett_ett__fem
               {"upTo5sec/ett_ett_ett_ett_ett__fem/ett_ett_ett_ett_ett__fem"},

               //euler31
               {"upTo5sec/euler31/euler31"},

               //euler_1
               {"upTo5sec/euler_1/euler_1"},

               //euler_6
               {"upTo5sec/euler_6/euler_6"},

               //euler_9
               {"upTo5sec/euler_9/euler_9"},

               //euler_18
               {"upTo5sec/euler_18/euler_18"},

               //euler_30
               {"upTo5sec/euler_30/euler_30"},

               //euler_39
               {"upTo30sec/euler_39/euler_39"},

               //eq10
               {"upTo5sec/eq10/eq10"},

               //evens
               {"upTo5sec/evens/evens"},

               //evision
               {"upTo5sec/evision/evision"},

               //exact_cover_dlx
               {"upTo5sec/exact_cover_dlx/exact_cover_dlx"},

               //exact_cover_dlx_matrix
               {"upTo5sec/exact_cover_dlx_matrix/exact_cover_dlx_matrix"},

               //exodus
               {"upTo5sec/exodus/exodus"},

               //eyedrop_optimize
               {"upTo5sec/eyedrop_optimize/eyedrop_optimize"},

               //eyedrop_optimize2
               {"upTo5sec/eyedrop_optimize2/eyedrop_optimize2"},

               //facility_location_problem
               {"upTo5sec/facility_location_problem/facility_location_problem"},

               //factorial
               {"upTo5sec/factorial/factorial"},

               //fair_split_into_3_groups
               {"upTo5sec/fair_split_into_3_groups/fair_split_into_3_groups"},

               //fair_xmas_duty_2014
               {"upTo5sec/fair_xmas_duty_2014/fair_xmas_duty_2014"},

               //fairies
               {"upTo5sec/fairies/fairies"},

               //family
               {"upTo5sec/family/family"},

               //family_riddle
               {"upTo5sec/family_riddle/family_riddle"},

               //fancy
               {"upTo5sec/fancy/fancy"},

               //farm_puzzle
               {"upTo5sec/farm_puzzle/farm_puzzle"},

               //farm_puzzle0
               {"upTo5sec/farm_puzzle0/farm_puzzle0"},

               //fib_test2
               {"upTo5sec/fib_test2/fib_test2"},

               //fill_in_the_squares
               {"upTo5sec/fill_in_the_squares/fill_in_the_squares"},

               //finding_celebrities
               {"upTo5sec/finding_celebrities/finding_celebrities"},

               //finding_celebrities2
               {"upTo5sec/finding_celebrities2/finding_celebrities2"},

               //five
               {"upTo5sec/five/five"},

               //five_brigades
               {"/upTo5sec/five_brigades/five_brigades"},

               //five_elements
               {"upTo5sec/five_elements/five_elements"},

               //five_floors
               {"upTo5sec/five_floors/five_floors"},

               //five_statements
               {"upTo5sec/five_statements/five_statements"},

               //five_translators
               {"upTo5sec/five_translators/five_translators"},

               //five_translators2
               {"upTo5sec/five_translators2/five_translators2"},

               //fix_points
               {"upTo5sec/fix_points/fix_points"},

               //fixed_charge
               {"upTo5sec/fixed_charge/fixed_charge"},

               //fizz_buzz
               {"upTo5sec/fizz_buzz/fizz_buzz"},

               //football
               {"upTo5sec/football/football"},

               //four_islands
               {"upTo5sec/four_islands/four_islands"},

               //four_numbers
               {"upTo5sec/four_numbers/four_numbers"},

               //four_same_friends
               {"upTo5sec/four_same_friends/four_same_friends"},

               //four_trees
               {"upTo5sec/four_trees/four_trees"},

               //fractions
               {"upTo5sec/fractions/fractions"},

               //franklin_8x8_magic_square
               {"upTo5sec/franklin_8x8_magic_square/franklin_8x8_magic_square"},

               //freight_transfer
               {"upTo5sec/freight_transfer/freight_transfer"},

               //full_adder
               {"upTo5sec/full_adder/full_adder"},

               //funny_dice
               {"upTo5sec/funny_dice/funny_dice"},

               //furniture_moving
               {"upTo5sec/furniture_moving/furniture_moving"},

               //gap
               {"upTo1min/gap/gap"},

               //gardner_dinner
               {"upTo5sec/gardner_dinner/gardner_dinner"},

               //gardner_sum_square
               {"upTo5sec/gardner_sum_square/gardner_sum_square"},

               //gardner_two_plus_two
               {"upTo5sec/gardner_two_plus_two/gardner_two_plus_two"},

               //gather_homage_martin
               {"upTo5sec/gather_homage_martin/gather_homage_martin"},


               //general_store
               {"upTo5sec/general_store/general_store"},

               //generalized_knapsack_problem
               {"upTo5sec/generalized_knapsack_problem/generalized_knapsack_problem"},

               //geost_test
               {"upTo5sec/geost_test/geost_test"},

               //giapetto
               {"upTo5sec/giapetto/giapetto"},

               //global_cardinality_no_loop
               {"upTo5sec/global_cardinality_no_loop/global_cardinality_no_loop"},

               //global_cardinality_table
               {"upTo5sec/global_cardinality_table/global_cardinality_table"},

               //global_cardinality_with_costs
               {"upTo5sec/global_cardinality_with_costs/global_cardinality_with_costs"},

               //global_contiguity
               {"upTo5sec/global_contiguity/global_contiguity"},

               //global_contiguity2
               {"upTo5sec/global_contiguity2/global_contiguity2"},

               //golden_search
               {"upTo5sec/golden_search/golden_search"},

               //golden_spiral
               {"upTo5sec/golden_spiral/golden_spiral"},

               //golf_puzzle
               {"upTo5sec/golf_puzzle/golf_puzzle"},

               //good_burger_puzzlor
               {"upTo5sec/good_burger_puzzlor/good_burger_puzzlor"},

               //graceful_labeling
               {"upTo5sec/graceful_labeling/graceful_labeling"},

               //graph_degree_sequence
               {"upTo5sec/graph_degree_sequence/graph_degree_sequence"},

               //graph_partition
               {"upTo5sec/graph_partition/graph_partition"},

               //gray_code
               {"upTo5sec/gray_code/gray_code"},

               //greatest_combination
               {"upTo5sec/greatest_combination/greatest_combination"},

               //grid_puzzle
               {"upTo5sec/grid_puzzle/grid_puzzle"},

               //grime_puzzle
               {"upTo5sec/grime_puzzle/grime_puzzle"},

               //langford2
               {"upTo5sec/langford2/langford2"},

               //langford_generalized
               {"upTo5sec/langford_generalized/langford_generalized"},

               //language_round_table
               {"upTo5sec/language_round_table/language_round_table"},

               //laplace
               //diferent result{"upTo5sec/laplace/laplace"},

               //latin_square
               {"upTo5sec/latin_square/latin_square"},

               //latin_square_card_puzzle
               {"upTo5sec/latin_square_card_puzzle/latin_square_card_puzzle"},

               //lccoin
               {"upTo5sec/lccoin/lccoin"},

               //leap_year
               {"upTo5sec/leap_year/leap_year"},

               //least_diff
               {"upTo5sec/least_diff/least_diff"},

               //least_diff1
               {"upTo5sec/least_diff1/least_diff1"},

               //lecture_series
               {"upTo5sec/lecture_series/lecture_series"},

               //lectures
               {"upTo5sec/lectures/lectures"},

               //lex2_me
               {"upTo5sec/lex2_me/lex2_me"},

               //lex_alldifferent
               {"upTo5sec/lex_alldifferent/lex_alldifferent"},

               //lex_between
               {"upTo5sec/lex_between/lex_between"},

               //lex_chain_less
               {"upTo5sec/lex_chain_less/lex_chain_less"},

               //lex_different
               {"upTo5sec/lex_different/lex_different"},

               //lex_greater_me
               {"upTo5sec/lex_greater_me/lex_greater_me"},

               //library_books
               {"upTo5sec/library_books/library_books"},

               //lichtenstein_coloring
               {"upTo5sec/lichtenstein_coloring/lichtenstein_coloring"},

               //life
               {"upTo5sec/life/life"},

               //lightmeal
               {"upTo5sec/lightmeal/lightmeal"},

               //lightmeal2
               {"upTo5sec/lightmeal2/lightmeal2"},

               //lights
               {"upTo5sec/lights/lights"},

               //lights_out
               {"upTo5sec/lights_out/lights_out"},

               //kqueens
               {"upTo30sec/kqueens/kqueens"},

               //limerick_primes
               {"upTo5sec/limerick_primes/limerick_primes"},

               //limerick_primes2
               {"upTo5sec/limerick_primes2/limerick_primes2"},

               //local_art_theft
               {"upTo5sec/local_art_theft/local_art_theft"},

               //local_art_theft1
               {"upTo5sec/local_art_theft1/local_art_theft1"},

               //locker
               {"upTo5sec/locker/locker"},

               //logic_puzzle_aop
               {"upTo5sec/logic_puzzle_aop/logic_puzzle_aop"},

               //logical_design
               {"upTo5sec/logical_design/logical_design"},

               //longest_change
               {"upTo5sec/longest_change/longest_change"},

               //lost_at_sea
               {"upTo5sec/lost_at_sea/lost_at_sea"},

               //lucky_number
               {"upTo5sec/lucky_number/lucky_number"},

               //M12
               {"upTo5sec/M12/M12"},

               //M12b
               {"upTo1min/M12b/M12b"},

               //m_queens_on_n_board
               {"upTo5sec/m_queens_on_n_board/m_queens_on_n_board"},

               //magic
               {"upTo5sec/magic/magic"},

               //magic3
               {"upTo5sec/magic3/magic3"},

               //magic4
               {"upTo5sec/magic4/magic4"},

               //magic_hexagon
               {"upTo5sec/magic_hexagon/magic_hexagon"},

               //magic_modulo_number
               {"upTo5sec/magic_modulo_number/magic_modulo_number"},

               //magic_sequence
               {"upTo5sec/magic_sequence/magic_sequence"},

               //magic_sequence2
               {"upTo5sec/magic_sequence2/magic_sequence2"},

               //magic_sequence3
               {"upTo5sec/magic_sequence3/magic_sequence3"},

               //grocery2
               {"upTo5sec/grocery2/grocery2"},

               //guards_and_apples
               {"upTo5sec/guards_and_apples/guards_and_apples"},

               //guards_and_apples2
               {"upTo5sec/guards_and_apples2/guards_and_apples2"},

               //gunport_problem1
               {"upTo30sec/gunport_problem1/gunport_problem1"},

               //gunport_problem2
               {"upTo5sec/gunport_problem2/gunport_problem2"},

               //hamming_distance
               {"upTo5sec/hamming_distance/hamming_distance"},

               //handshaking
               {"upTo5sec/handshaking/handshaking"},

               //hanging_weights
               {"upTo5sec/hanging_weights/hanging_weights"},

               //harry_potter_seven_potions
               {"upTo5sec/harry_potter_seven_potions/harry_potter_seven_potions"},

               //heterosquare
               {"upTo5sec/heterosquare/heterosquare"},


               //hidato_exists
               {"upTo5sec/hidato_exists/hidato_exists"},

               //hidato_table
               {"upTo30sec/hidato_table/hidato_table"},

               //hidato_table2
               {"upTo5sec/hidato_table2/hidato_table2"},

               //high_iq_problem
               {"upTo5sec/high_iq_problem/high_iq_problem"},

               //honey_division
               {"upTo5sec/honey_division/honey_division"},

               //houses
               {"upTo5sec/houses/houses"},

               //how_old_am_i
               {"upTo5sec/how_old_am_i/how_old_am_i"},

               //huey_dewey_louie
               {"upTo5sec/huey_dewey_louie/huey_dewey_louie"},

               //hundred_doors_optimized
               {"upTo5sec/hundred_doors_optimized/hundred_doors_optimized"},

               //hundred_doors_optimized_array
               {"upTo5sec/hundred_doors_optimized_array/hundred_doors_optimized_array"},

               //hundred_doors_unoptimized
               {"upTo5sec/hundred_doors_unoptimized/hundred_doors_unoptimized"},

               //hundred_doors_unoptimized2
               {"upTo5sec/hundred_doors_unoptimized2/hundred_doors_unoptimized2"},

               //hundred_fowls
               {"upTo5sec/hundred_fowls/hundred_fowls"},

               //imply
               {"upTo5sec/imply/imply"},

               //in_interval
               {"upTo5sec/in_interval/in_interval"},

               //in_relation
               {"upTo5sec/in_relation/in_relation"},

               //in_same_partition
               {"upTo5sec/in_same_partition/in_same_partition"},

               //in_set
               {"upTo5sec/in_set/in_set"},

               //increasing_except_0
               {"upTo5sec/increasing_except_0/increasing_except_0"},

               //indexed_sum
               {"upTo5sec/indexed_sum/indexed_sum"},

               //inflexions
               {"upTo5sec/inflexions/inflexions"},

               //int_value_precede
               {"upTo5sec/int_value_precede/int_value_precede"},

               //integer_programming1
               {"upTo5sec/integer_programming1/integer_programming1"},

               //inter_distance
               {"upTo5sec/inter_distance/inter_distance"},

               //inverse_within_range
               {"upTo5sec/inverse_within_range/inverse_within_range"},

               //investment_problem
               {"upTo5sec/investment_problem/investment_problem"},

               //investment_problem_mip
               {"upTo5sec/investment_problem_mip/investment_problem_mip"},

               //is_prime
               {"upTo5sec/is_prime/is_prime"},

               //isbn
               {"upTo5sec/isbn/isbn"},

               //itemset_mining
               {"upTo5sec/itemset_mining/itemset_mining"},

               //ith_pos_different_from_0
               {"upTo5sec/ith_pos_different_from_0/ith_pos_different_from_0"},

               //its_a_tie
               {"upTo5sec/its_a_tie/its_a_tie"},

               //jellybeans
               {"upTo5sec/jellybeans/jellybeans"},

               //jive_turkeys
               {"upTo5sec/jive_turkeys/jive_turkeys"},

               //jobs_puzzle
               {"upTo5sec/jobs_puzzle/jobs_puzzle"},

               //joshua
               {"upTo5sec/joshua/joshua"},

               //just_forgotten
               {"upTo5sec/just_forgotten/just_forgotten"},

               //K4P2GracefulGraph
               {"upTo5sec/K4P2GracefulGraph/K4P2GracefulGraph"},

               //K4P2GracefulGraph2
               {"upTo5sec/K4P2GracefulGraph2/K4P2GracefulGraph2"},

               //k_alldifferent
               {"upTo5sec/k_alldifferent/k_alldifferent"},

               //k_consecutive_integers
               {"upTo5sec/k_consecutive_integers/k_consecutive_integers"},

               //k_same
               {"upTo5sec/k_same/k_same"},

               //k_same_modulo
               {"upTo5sec/k_same_modulo/k_same_modulo"},

               //kakuro
               {"upTo5sec/kakuro/kakuro"},

               //kakuro2
               {"upTo5sec/kakuro2/kakuro2"},

               //kakuro3
               {"upTo5sec/kakuro3/kakuro3"},

               //kaprekars_constant
               {"upTo5sec/kaprekars_constant/kaprekars_constant"},

               //kaprekars_constant2
               {"upTo5sec/kaprekars_constant2/kaprekars_constant2"},

               //kenken2
               {"upTo5sec/kenken2//kenken2"},

               //killer_sudoku
               {"upTo5sec/killer_sudoku/killer_sudoku"},

               //killer_sudoku2
               {"upTo5sec/killer_sudoku2/killer_sudoku2"},

               //kiselman_semigroup_problem
               {"upTo5sec/kiselman_semigroup_problem/kiselman_semigroup_problem"},

               //knapsack
               {"upTo5sec/knapsack/knapsack"},

               //knapsack1
               {"upTo5sec/knapsack1/knapsack1"},

               //knapsack2
               {"upTo5sec/knapsack2/knapsack2"},

               //knapsack_investments
               {"upTo5sec/knapsack_investments/knapsack_investments"},

               //knapsack_problem
               {"upTo5sec/knapsack_problem/knapsack_problem"},

               //knapsack_rosetta_code_01
               {"upTo5sec/knapsack_rosetta_code_01/knapsack_rosetta_code_01"},

               //knapsack_rosetta_code_bounded
               {"upTo5sec/knapsack_rosetta_code_bounded/knapsack_rosetta_code_bounded"},



               //magic_series
               {"upTo5sec/magic_series/magic_series"},

               //magic_square
               {"upTo5sec/magic_square/magic_square"},

               //magic_square_frenicle_form
               {"upTo5sec/magic_square_frenicle_form/magic_square_frenicle_form"},

               //magic_square_function
               {"upTo5sec/magic_square_function/magic_square_function"},

               //magic_squares_and_cards
               {"upTo5sec/magic_squares_and_cards/magic_squares_and_cards"},

               //make_a_good_burger
               {"upTo5sec/make_a_good_burger/make_a_good_burger"},

               //mamas_age
               {"upTo5sec/mamas_age/mamas_age"},

               //manasa_and_stones
               {"upTo5sec/manasa_and_stones/manasa_and_stones"},

               //mango_puzzle
               {"upTo5sec/mango_puzzle/mango_puzzle"},

               //map
               {"upTo5sec/map/map"},

               //map2
               {"upTo5sec/map2/map2"},

               //map_coloring_with_costs
               {"upTo5sec/map_coloring_with_costs/map_coloring_with_costs"},

               //map_stuckey
               {"upTo5sec/map_stuckey/map_stuckey"},

               //marathon
               {"upTo5sec/marathon/marathon"},

               //marathon2
               {"upTo5sec/marathon2/marathon2"},

               //markov_chains
               {"upTo5sec/markov_chains/markov_chains"},

               //markov_chains_taha
               {"upTo5sec/markov_chains_taha/markov_chains_taha"},

               //matching_sums
               {"upTo5sec/matching_sums/matching_sums"},

               //matchmaker
               {"upTo5sec/matchmaker/matchmaker"},

               //matrix2num
               {"upTo5sec/matrix2num/matrix2num"},

               //mats_fotboll
               {"upTo5sec/mats_fotboll/mats_fotboll"},

               //max_activity
               {"upTo5sec/max_activity/max_activity"},

               //max_activity2
               {"upTo5sec/max_activity2/max_activity2"},

               //max_cut
               {"upTo5sec/max_cut/max_cut"},

               //max_flow_taha
               {"upTo5sec/max_flow_taha/max_flow_taha"},

               //max_flow_winston1
               {"upTo5sec/max_flow_winston1/max_flow_winston1"},

               //max_index
               {"upTo5sec/max_index/max_index"},

               //max_m_in_row
               {"upTo5sec/max_m_in_row/max_m_in_row"},

               //max_n
               {"upTo5sec/max_n/max_n"},

               //max_size_of_consecutive_var
               {"upTo5sec/max_size_of_consecutive_var/max_size_of_consecutive_var"},

               //max_size_set_of_consecutive_var
               {"upTo5sec/max_size_set_of_consecutive_var/max_size_set_of_consecutive_var"},

               //maximum_density_still_life
               {"upTo5sec/maximum_density_still_life/maximum_density_still_life"},

               //maximum_modulo
               {"upTo5sec/maximum_modulo/maximum_modulo"},

               //maximum_subarray
               {"upTo5sec/maximum_subarray/maximum_subarray"},

               //message_sending
               {"upTo5sec/message_sending/message_sending"},

               //mfasp
               {"upTo5sec/mfasp/mfasp"},

               //mfvsp
               {"upTo5sec/mfvsp/mfvsp"},

               //min_index
               {"upTo5sec/min_index/min_index"},

               //min_max_sets
               {"upTo5sec/min_max_sets/min_max_sets"},

               //min_n
               {"upTo5sec/min_n/min_n"},

               //min_nvalue
               {"upTo5sec/min_nvalue/min_nvalue"},

               //minesweeper
               {"upTo5sec/minesweeper/minesweeper"},

               //minesweeper_0
               {"upTo5sec/minesweeper_0/minesweeper_0"},

               //minesweeper_1
               {"upTo5sec/minesweeper_1/minesweeper_1"},

               //minesweeper_2
               {"upTo5sec/minesweeper_2/minesweeper_2"},

               //minesweeper_3
               {"upTo5sec/minesweeper_3/minesweeper_3"},

               //minesweeper_4
               {"upTo5sec/minesweeper_4/minesweeper_4"},

               //minesweeper_5
               {"upTo5sec/minesweeper_5/minesweeper_5"},

               //minesweeper_6
               {"upTo5sec/minesweeper_6/minesweeper_6"},

               //minesweeper_7
               {"upTo5sec/minesweeper_7/minesweeper_7"},

               //minesweeper_8
               {"upTo5sec/minesweeper_8/minesweeper_8"},

               //minesweeper_9
               {"upTo5sec/minesweeper_9/minesweeper_9"},

               //minesweeper_basic3
               {"upTo5sec/minesweeper_basic3/minesweeper_basic3"},

               //minesweeper_basic4
               {"upTo5sec/minesweeper_basic4/minesweeper_basic4"},

               //minesweeper_basic4x4
               {"upTo5sec/minesweeper_basic4x4/minesweeper_basic4x4"},

               //minesweeper_config_page2
               {"upTo5sec/minesweeper_config_page2/minesweeper_config_page2"},

               //minesweeper_config_page3
               {"upTo5sec/minesweeper_config_page3/minesweeper_config_page3"},

               //minesweeper_german_Lakshtanov
               {"upTo5sec/minesweeper_german_Lakshtanov/minesweeper_german_Lakshtanov"},

               //minesweeper_inverse
               {"upTo5sec/minesweeper_inverse/minesweeper_inverse"},

               //minesweeper_splitter
               {"upTo5sec//minesweeper_splitter/minesweeper_splitter"},

               //minesweeper_wire
               {"upTo5sec/minesweeper_wire/minesweeper_wire"},

               //minimal_subset_of_columns
               {"upTo5sec/minimal_subset_of_columns/minimal_subset_of_columns"},

               //minimum_except_0
               {"upTo5sec/minimum_except_0/minimum_except_0"},

               //minimum_greater_than
               {"upTo5sec/minimum_greater_than/minimum_greater_than"},

               //minimum_weight_alldifferent
               {"upTo5sec/minimum_weight_alldifferent/minimum_weight_alldifferent"},

               //minsum
               {"upTo5sec/minsum/minsum"},

               //mislabeled_boxes
               {"upTo5sec/mislabeled_boxes/mislabeled_boxes"},

               //misp
               {"upTo5sec/misp/misp"},

               //monkey_coconuts
               {"upTo5sec/monkey_coconuts/monkey_coconuts"},

               //monks_and_doors
               {"upTo5sec/monks_and_doors/monks_and_doors"},

               //monorail
               {"upTo5sec/monorail/monorail6"},

               //movement_puzzle
               {"upTo5sec/movement_puzzle/movement_puzzle"},

               //movie_scheduling
               {"upTo5sec/movie_scheduling/movie_scheduling"},

               //movie_stars
               {"upTo5sec/movie_stars/movie_stars"},

               //mr_smith
               {"upTo5sec/mr_smith/mr_smith"},

               //muddle_management
               {"upTo5sec/muddle_management/muddle_management"},

               //upTo5sec
               {"upTo5sec/multipl/multipl"},

               //reveal_the_mapping
               {"upTo5sec/reveal_the_mapping/reveal_the_mapping"},

               //reverse_multiples
               {"upTo5sec/reverse_multiples/reverse_multiples"},

               //rock_star_dressing_problem
               {"upTo5sec/rock_star_dressing_problem/rock_star_dressing_problem"},

               //rook_path
               {"upTo5sec/rook_path/rook_path"},

               //rookwise_chain
               {"upTo5sec/rookwise_chain/rookwise_chain"},

               //roots_test
               {"upTo5sec/roots_test/roots_test"},

               //monorail
               {"upTo1min/monorail/monorail3"},
               {"upTo1hour/monorail/monorail4"},
               {"upTo5sec/monorail/monorail6"},

               //numberlink
               {"upTo5sec/numberlink/numberlink1"},
               {"upTo5sec/numberlink/numberlink3"},

               //scheduling_with_assignments
               {"upTo5sec/scheduling_with_assignments/scheduling_with_assignments1"},
               {"upTo5sec/scheduling_with_assignments/scheduling_with_assignments2"},
               {"upTo5sec/scheduling_with_assignments/scheduling_with_assignments3"},
               {"upTo5sec/scheduling_with_assignments/scheduling_with_assignments4"},
               {"upTo5sec/scheduling_with_assignments/scheduling_with_assignments6"},
               {"upTo5sec/scheduling_with_assignments/scheduling_with_assignments11"},
               {"upTo5sec/scheduling_with_assignments/scheduling_with_assignments12"},
               {"upTo5sec/scheduling_with_assignments/scheduling_with_assignments13"},
               {"upTo1hour/scheduling_with_assignments/scheduling_with_assignments14"},
               {"upTo5sec/scheduling_with_assignments/scheduling_with_assignments15"},
               {"upTo5sec/scheduling_with_assignments/scheduling_with_assignments16"},
               {"upTo5sec/scheduling_with_assignments/scheduling_with_assignments16e2"},
               {"upTo5sec/scheduling_with_assignments/scheduling_with_assignments16g"},
               {"upTo5sec/scheduling_with_assignments/scheduling_with_assignments17"},
               {"upTo5sec/scheduling_with_assignments/scheduling_with_assignments18"},
               {"upTo5sec/scheduling_with_assignments/scheduling_with_assignments19"},
               {"upTo5sec/scheduling_with_assignments/scheduling_with_assignments20"},
               {"upTo5sec/scheduling_with_assignments/scheduling_with_assignments21"},

               //kntdom
               {"upTo1hour/kntdom/kntdom"},

               //kraftwerk_ticket_problem
               {"above1hour/kraftwerk_ticket_problem/kraftwerk_ticket_problem"},

               //max_nvalue
               {"upTo5sec/max_nvalue/max_nvalue"},

               //maxflow
               {"upTo5sec/maxflow/maxflow"},

               //maximal_independent_sets
               {"upTo1hour/maximal_independent_sets/maximal_independent_sets"},

               //monorail
               {"above1hour/monorail/monorail4"},

               //a_card_trick_1
               {"above1hour/a_card_trick_1/a_card_trick_1"},

               //autoref
               {"upTo10min/autoref/autoref"},

               //music_men
               {"upTo5sec/music_men/music_men"},

               //mvcp
               {"upTo5sec/mvcp/mvcp"},

               //my_nvalue
               {"upTo5sec/my_nvalue/my_nvalue"},

               //my_precedence
               {"upTo5sec/my_precedence/my_precedence"},

               //n_change
               {"upTo5sec/n_change//n_change"},

               //n_partitioning
               {"upTo5sec/n_partitioning/n_partitioning"},

               //n_puzzle
               {"upTo5sec/n_puzzle/n_puzzle"},

               //nadel
               {"upTo5sec/nadel/nadel"},

               //narcissistic_numbers
               {"upTo5sec/narcissistic_numbers/narcissistic_numbers"},

               //nchange
               {"upTo5sec/nchange/nchange"},

               //nclass
               {"upTo5sec/nclass/nclass"},

               //nequivalence
               {"upTo5sec/nequivalence/nequivalence"},

               //newspaper
               {"upTo5sec/newspaper/newspaper"},

               //newspaper0
               {"upTo5sec/newspaper0/newspaper0"},

               //next_element
               {"upTo5sec/next_element/next_element"},

               //next_greater_element
               {"upTo5sec/next_greater_element/next_greater_element"},

               //nim
               {"upTo5sec/nim/nim"},

               //nine_digit_arrangement
               {"upTo5sec/nine_digit_arrangement/nine_digit_arrangement"},

               //nine_to_one_equals_100
               {"upTo5sec/nine_to_one_equals_100/nine_to_one_equals_100"},

               //no_three_in_line
               {"upTo5sec/no_three_in_line/no_three_in_line"},

               //non_dominating_queens
               {"upTo5sec/non_dominating_queens/non_dominating_queens"},

               //work_shift_problem
               {"upTo5sec/work_shift_problem/work_shift_problem"},

               //wwr
               {"upTo5sec/wwr/wwr"},

               //xkcd
               {"upTo5sec/xkcd/xkcd"},

               //xkcd_among_diff_0
               {"upTo5sec/xkcd_among_diff_0/xkcd_among_diff_0"},

               //young_tableaux
               {"upTo5sec/young_tableaux/young_tableaux"},

               //coins_problem
               {"upTo10min/coins_problem/coins_problem"},

               //company_competition
               {"upTo5sec/company_competition/company_competition"},

               //multiplicative_sequence
               {"upTo5sec/multiplicative_sequence/multiplicative_sequence"},

               //murder
               {"upTo5sec/murder/murder"},

               //not_all_equal
               {"upTo5sec/not_all_equal/not_all_equal"},

               //not_in
               {"upTo5sec/not_in/not_in"},

               //npair
               {"upTo5sec/npair/npair"},

               //number_generation
               {"upTo5sec/number_generation/number_generation"},

               //number_of_days
               {"upTo5sec/number_of_days/number_of_days"},

               //number_of_regions
               {"upTo5sec/number_of_regions/number_of_regions"},

               //numbrix
               {"upTo5sec/numbrix/numbrix"},

               //numeric_keypad
               {"upTo5sec/numeric_keypad/numeric_keypad"},

               //numerica_p19
               {"upTo5sec/numerica_p19/numerica_p19"},

               //numerica_p20
               {"upTo5sec/numerica_p20/numerica_p20"},

               //numerica_p21
               {"upTo5sec/numerica_p21/numerica_p21"},

               //numerica_p23
               {"upTo5sec/numerica_p23/numerica_p23"},

               //numerica_p24
               {"upTo5sec/numerica_p24/numerica_p24"},

               //nurse_rostering_with_availability
               {"upTo5sec/nurse_rostering_with_availability/nurse_rostering_with_availability"},

               //nvalue_on_intersection
               {"upTo5sec/nvalue_on_intersection/nvalue_on_intersection"},

               //nvalues
               {"upTo5sec/nvalues/nvalues"},

               //nvalues_except_0
               {"upTo5sec/nvalues_except_0/nvalues_except_0"},

               //OandX
               {"upTo5sec/OandX/OandX"},

               //office_blocked
               {"upTo5sec/office_blocked/office_blocked"},

               //office_blocked2
               {"upTo5sec/office_blocked2/office_blocked2"},

               //olympic
               {"upTo5sec/olympic/olympic"},

               //one_off_digit
               {"upTo5sec/one_off_digit/one_off_digit"},

               //onroad
               {"upTo5sec/onroad/onroad"},

               //open_alldifferent
               {"upTo5sec/open_alldifferent/open_alldifferent"},

               //open_among
               {"upTo5sec/open_among/open_among"},

               //open_atleast
               {"upTo5sec/open_atleast/open_atleast"},

               //open_atmost
               // {"upTo5sec/open_atmost/open_atmost"},

               //open_global_cardinality
               {"upTo5sec/open_global_cardinality/open_global_cardinality"},

               //open_global_cardinality_low_up
               {"upTo5sec/open_global_cardinality_low_up/open_global_cardinality_low_up"},

               //optimal_picking_elements_from_each_list
               {"upTo30sec/optimal_picking_elements_from_each_list/optimal_picking_elements_from_each_list"},

               //jssp
               {"upTo1hour/jssp/jssp"},

               //or_matching
               {"upTo5sec/or_matching/or_matching"},

               //or_matching_orig
               {"upTo5sec/or_matching_orig/or_matching_orig"},

               //or_seating
               {"upTo1min/or_seating/or_seating"},

               //ordering_a_list_of_lists
               {"upTo5sec/ordering_a_list_of_lists/ordering_a_list_of_lists"},

               //organize_day
               {"upTo5sec/organize_day/organize_day"},

               //ormat_game_generate
               {"upTo5sec/ormat_game_generate/ormat_game_generate"},

               //orth_link_ori_siz_end
               {"upTo5sec/orth_link_ori_siz_end/orth_link_ori_siz_end"},

               //orth_on_the_ground
               {"upTo5sec/orth_on_the_ground/orth_on_the_ground"},

               //p_median
               {"upTo5sec/p_median/p_median"},

               //pair_divides_the_sum
               {"upTo5sec/pair_divides_the_sum/pair_divides_the_sum"},

               //upTo5sec
               {"upTo5sec/pairwise_sum_of_n_numbers/pairwise_sum_of_n_numbers"},

               //rostering
               {"upTo5sec/rostering/rostering"},

               //rot13
               {"upTo5sec/rot13/rot13"},

               //rot13_2
               {"upTo30sec/rot13_2/rot13_2"},

               //rotating_discs
               {"upTo5sec/rotating_discs/rotating_discs"},

               //rotation
               {"upTo30sec/rotation/rotation"},

               //numberlink7
               {"upTo5sec/numberlink/numberlink7"},

               //autoref
               {"upTo10min/autoref/autoref"},

               //dqueens
               {"upTo5min/dqueens/dqueens"},

               //dudeney_bishop_placement1
               {"upTo10min/dudeney_bishop_placement1/dudeney_bishop_placement1"},

               //equal_sized_groups
               {"upTo5min/equal_sized_groups/equal_sized_groups"},

               //evens2
               {"upTo5sec/evens2/evens2"},

               //futoshiki
               {"upTo5sec//futoshiki/futoshiki"},

               //gardner_prime_puzzle
               {"upTo5sec/gardner_prime_puzzle/gardner_prime_puzzle"},

               //gcd_lcm
               {"upTo5sec/gcd_lcm/gcd_lcm"},

               //hidato
               {"upTo5min/hidato/hidato"},

               //jobshop
               {"upTo5sec/jobshop/jobshop_mt06"},
               {"upTo5sec/jobshop/jobshop_newspaper"},

               //jobshop2
               {"upTo5sec/jobshop2/jobshop2_mt06"},
               {"upTo5sec/jobshop2/jobshop2_newspaper"},

               //parallel_resistors
               {"upTo5sec/parallel_resistors//parallel_resistors"},

               //partial_latin_square
               {"upTo5sec/partial_latin_square/partial_latin_square"},

               //partition_into_subset_of_equal_values
               {"upTo5sec/partition_into_subset_of_equal_values/partition_into_subset_of_equal_values"},

               //partition_into_subset_of_equal_values2
               {"upTo5sec/partition_into_subset_of_equal_values2/partition_into_subset_of_equal_values2"},

               //partition_into_subset_of_equal_values3
               {"upTo5sec//partition_into_subset_of_equal_values3/partition_into_subset_of_equal_values3"},

               //partitions
               {"upTo5sec/partitions/partitions"},

               //nonlin_cylinder
               {"upTo5sec/nonlin_cylinder/nonlin_cylinder"},

               //path_from_to
               {"upTo5sec/path_from_to/path_from_to"},

               //patient_no_21
               {"upTo5sec/patient_no_21/patient_no_21"},

               //pchange
               {"upTo5sec/pchange/pchange"},

               //peacableArmyOfQueens
               {"upTo5sec/peacableArmyOfQueens/peacableArmyOfQueens"},

               //penguin
               {"upTo5sec/penguin//penguin"},

               //perfect_shuffle
               {"upTo5sec/perfect_shuffle/perfect_shuffle"},

               //period
               {"upTo5sec/period/period"},

               //permutation_number
               {"upTo5sec/permutation_number/permutation_number"},

               //pert
               {"upTo5sec/pert/pert"},

               //philosophical_railway
               {"upTo5sec/philosophical_railway/philosophical_railway"},

               //photo_hkj
               {"upTo5sec/photo_hkj/photo_hkj"},

               //photo_hkj2_data1
               {"upTo5sec/photo_hkj2_data1/photo_hkj2_data1"},

               //photo_hkj2_data2
               {"upTo5sec/photo_hkj2_data2/photo_hkj2_data2"},

               //pigeon_hole
               {"upTo5sec/pigeon_hole/pigeon_hole"},

               //pigeon_hole2
               {"upTo5sec/pigeon_hole2/pigeon_hole2"},

               //pilgrim
               {"upTo5sec/pilgrim/pilgrim"},

               //place_number
               {"upTo5sec/place_number/place_number"},

               //place_number2
               {"upTo5sec/place_number2/place_number2"},

               //planet_colonization_puzzlor
               {"upTo5sec/planet_colonization_puzzlor/planet_colonization_puzzlor"},

               //pool_ball_triangles
               {"upTo5sec/pool_ball_triangles/pool_ball_triangles"},

               //popsicle_stand
               {"upTo5sec/popsicle_stand/popsicle_stand"},

               //post_office_problem
               {"upTo5sec/post_office_problem/post_office_problem"},

               //post_office_problem2
               {"upTo5sec/post_office_problem2/post_office_problem2"},

               //power
               {"upTo5sec/power/power"},

               //power_set
               {"upTo5sec/power_set/power_set"},

               //power_set2
               {"upTo5sec/power_set2/power_set2"},

               //power_set3
               {"upTo5sec/power_set3/power_set3"},

               //prime
               {"upTo5sec/prime/prime"},

               //prime_looking
               {"upTo5sec/prime_looking/prime_looking"},

               //prime_multiplication
               {"upTo5sec/prime_multiplication/prime_multiplication"},

               //primes
               {"upTo5sec/primes/primes"},

               //primes_in_a_circle
               {"upTo5sec/primes_in_a_circle/primes_in_a_circle"},

               //primes_param
               {"upTo5sec/primes_param/primes_param"},

               //product_test
               {"upTo5sec/product_test/product_test"},

               //puzzle1
               {"upTo5sec/puzzle1/puzzle1"},

               //pyramid_of_numbers
               {"upTo5sec/pyramid_of_numbers/pyramid_of_numbers"},

               //quasiGroup3Idempotent
               {"upTo5sec/quasiGroup3Idempotent/quasiGroup3Idempotent"},

               //quasiGroup3NonIdempotent
               {"upTo5sec/quasiGroup3NonIdempotent/quasiGroup3NonIdempotent"},

               //quasiGroup4Idempotent
               {"upTo5sec/quasiGroup4Idempotent/quasiGroup4Idempotent"},

               //quasiGroup4NonIdempotent
               {"upTo5sec/quasiGroup4NonIdempotent/quasiGroup4NonIdempotent"},

               //quasiGroup5Idempotent
               {"upTo5sec/quasiGroup5Idempotent/quasiGroup5Idempotent"},

               //quasiGroup5NonIdempotent
               {"upTo5sec/quasiGroup5NonIdempotent/quasiGroup5NonIdempotent"},

               //quasiGroup6
               {"upTo5sec/quasiGroup6/quasiGroup6"},

               //quasiGroup7
               {"upTo5sec/quasiGroup7/quasiGroup7"},

               //quasigroup_completion
               {"upTo5sec/quasigroup_completion/quasigroup_completion"},

               //quasigroup_completion_gcc
               {"upTo5sec/quasigroup_completion_gcc/quasigroup_completion_gcc"},

               //quasigroup_completion_gomes_demo1
               {"upTo5sec/quasigroup_completion_gomes_demo1/quasigroup_completion_gomes_demo1"},

               //quasigroup_completion_gomes_demo2
               {"upTo5sec/quasigroup_completion_gomes_demo2/quasigroup_completion_gomes_demo2"},

               //quasigroup_completion_gomes_demo3
               {"upTo5sec/quasigroup_completion_gomes_demo3/quasigroup_completion_gomes_demo3"},

               //quasigroup_completion_gomes_demo4
               {"upTo5sec/quasigroup_completion_gomes_demo4/quasigroup_completion_gomes_demo4"},

               //quasigroup_completion_gomes_shmoys_p3
               {"upTo5sec/quasigroup_completion_gomes_shmoys_p3/quasigroup_completion_gomes_shmoys_p3"},

               //quasigroup_completion_gomes_shmoys_p7
               {"upTo5sec/quasigroup_completion_gomes_shmoys_p7/quasigroup_completion_gomes_shmoys_p7"},

               //quasigroup_completion_martin_lynce
               {"upTo5sec/quasigroup_completion_martin_lynce/quasigroup_completion_martin_lynce"},

               //queens3
               {"upTo5sec/queens3/queens3"},

               //queens4
               {"upTo5sec/queens4/queens4"},

               //queens_and_knights
               {"upTo5sec/queens_and_knights/queens_and_knights"},

               //queens_ip
               {"upTo5sec/queens_ip/queens_ip"},

               //ramsey_partition
               {"upTo5sec/ramsey_partition/ramsey_partition"},

               //random_function_test
               {"upTo5sec/random_function_test/random_function_test"},

               //random_generator
               {"upTo5sec/random_generator/random_generator"},

               //random_generator2
               {"upTo5sec/random_generator2/random_generator2"},

               //random_set
               {"upTo5sec/random_set/random_set"},

               //range_ctr
               {"upTo5sec/range_ctr/range_ctr"},

               //raven_puzzle
               {"upTo5sec/raven_puzzle/raven_puzzle"},

               //rectangle_from_line_segments
               {"upTo5sec/rectangle_from_line_segments/rectangle_from_line_segments"},

               //relative_sizes
               {"upTo5sec/relative_sizes/relative_sizes"},

               //relief_mission
               {"upTo5sec/relief_mission/relief_mission"},

               //remainder_puzzle
               {"upTo5sec/remainder_puzzle/remainder_puzzle"},

               //remainder_puzzle2
               {"upTo5sec/remainder_puzzle2/remainder_puzzle2"},

               //runs
               {"upTo5sec/runs/runs"},

               //safe_cracking
               {"upTo5sec/safe_cracking/safe_cracking"},

               //same
               {"upTo5sec/same/same"},

               //same_and_global_cardinality
               {"upTo5sec/same_and_global_cardinality/same_and_global_cardinality"},

               //same_and_global_cardinality_low_up
               {"upTo5sec/same_and_global_cardinality_low_up/same_and_global_cardinality_low_up"},

               //same_interval
               {"upTo5sec/same_interval/same_interval"},

               //same_modulo
               {"upTo5sec/same_modulo/same_modulo"},

               //samurai_puzzle
               {"upTo5sec/samurai_puzzle/samurai_puzzle"},

               //sangraal
               {"upTo5sec/sangraal/sangraal"},

               //sangraal_cp
               {"upTo5sec/sangraal_cp/sangraal_cp"},

               //sat
               {"upTo5sec/sat/sat"},

               //satisfy
               {"upTo5sec/satisfy/satisfy"},

               //upTo5sec
               {"upTo5sec/scalar_product/scalar_product"},

               //scanner_problem
               {"upTo5sec/scanner_problem/scanner_problem"},

               //scene_allocation
               {"upTo1min/scene_allocation/scene_allocation"},

               //schedule1
               {"upTo5sec/schedule1/schedule1"},

               //schedule2
               {"upTo5sec/schedule2/schedule2"},

               //scheduling_bratko
               {"upTo5sec/scheduling_bratko/scheduling_bratko"},

               //scheduling_bratko2
               {"upTo5sec/scheduling_bratko2/scheduling_bratko2"},

               //scheduling_chip
               {"upTo5sec/scheduling_chip/scheduling_chip"},

               //scheduling_speakers
               {"upTo5sec/scheduling_speakers/scheduling_speakers"},

               //scheduling_speakers_optimize
               {"upTo5sec/scheduling_speakers_optimize/scheduling_speakers_optimize"},

               //seating_plan
               {"upTo5sec/seating_plan/seating_plan"},

               //seating_row
               {"upTo5sec/seating_row/seating_row"},

               //seating_row1
               {"upTo5sec/seating_row1/seating_row1"},

               //seating_table
               {"upTo5sec/seating_table/seating_table"},

               //secret_santa
               {"upTo5sec/secret_santa/secret_santa"},

               //upTo5sec
               {"upTo5sec/secret_santa2/secret_santa2"},

               //self_referential_quiz
               {"upTo5sec/self_referential_quiz/self_referential_quiz"},

               //self_referential_sentence
               {"upTo5sec/self_referential_sentence/self_referential_sentence"},

               //send_more_money
               {"upTo5sec/send_more_money/send_more_money"},

               //send_more_money2
               {"upTo5sec/send_more_money2/send_more_money2"},

               //send_more_money_any_base
               {"upTo5sec/send_more_money_any_base/send_more_money_any_base"},

               //send_more_money_ip
               {"upTo5sec/send_more_money_ip/send_more_money_ip"},

               //send_most_money
               {"upTo5sec/send_most_money/send_most_money"},

               //separate_zeros
               {"upTo5sec/separate_zeros/separate_zeros"},

               //sequence_2_3
               {"upTo5sec/sequence_2_3/sequence_2_3"},

               //seseman
               {"upTo5sec/seseman/seseman"},

               //seseman2
               {"upTo5sec/seseman2/seseman2"},

               //set_covering
               {"upTo5sec/set_covering/set_covering"},

               //set_covering2
               {"upTo5sec/set_covering2/set_covering2"},

               //set_covering3
               {"upTo5sec/set_covering3/set_covering3"},

               //set_covering4
               {"upTo5sec/set_covering4/set_covering4"},

               //set_covering4b
               {"upTo5sec/set_covering4b/set_covering4b"},

               //set_covering5
               {"upTo5sec/set_covering5/set_covering5"},

               //set_covering6
               {"upTo5sec/set_covering6/set_covering6"},

               //set_covering_deployment
               {"upTo5sec/set_covering_deployment/set_covering_deployment"},

               //set_covering_opl
               {"upTo5sec/set_covering_opl/set_covering_opl"},

               //set_covering_skiena
               {"upTo5sec/set_covering_skiena/set_covering_skiena"},

               //set_packing
               {"upTo5sec/set_packing/set_packing"},

               //set_partition
               {"upTo5sec/set_partition/set_partition"},

               //set_partition_stackoverflow
               {"upTo5sec/set_partition_stackoverflow/set_partition_stackoverflow"},

               //set_puzzle
               {"upTo5sec/set_puzzle/set_puzzle"},

               //shift
               {"upTo5sec/shift/shift"},

               //shopping
               {"upTo5sec/shopping/shopping"},

               //shopping_basket
               {"upTo5sec/shopping_basket/shopping_basket"},

               //shopping_basket2
               {"upTo5sec/shopping_basket2/shopping_basket2"},

               //shopping_basket5
               {"upTo5sec/shopping_basket5/shopping_basket5"},

               //shopping_basket6
               {"upTo5sec/shopping_basket6/shopping_basket6"},

               //shortest_path1
               {"upTo5sec/shortest_path1/shortest_path1"},

               //shortest_path2
               {"upTo5sec/shortest_path2/shortest_path2"},

               //sicherman_dice
               {"upTo5sec/sicherman_dice/sicherman_dice"},

               //sieve
               {"upTo5sec/sieve/sieve"},

               //ski_assignment
               {"upTo5sec/ski_assignment/ski_assignment"},

               //ski_assignment_problem
               {"upTo5sec/ski_assignment_problem/ski_assignment_problem"},

               //skyscraper
               {"upTo5sec/skyscraper/skyscraper"},

               //sliding_sum_me
               {"upTo5sec/sliding_sum_me/sliding_sum_me"},

               //sliding_time_window
               {"upTo5sec/sliding_time_window/sliding_time_window"},

               //sliding_time_window_from_start
               {"upTo5sec/sliding_time_window_from_start/sliding_time_window_from_start"},

               //smallest_winning_electoral
               {"upTo30sec/smallest_winning_electoral/smallest_winning_electoral"},

               //smooth
               {"upTo30sec/smooth/smooth"},

               //smuggler_knapsack
               {"upTo5sec/smuggler_knapsack/smuggler_knapsack"},

               //smullyan_knights_knaves
               {"upTo5sec/smullyan_knights_knaves/smullyan_knights_knaves"},

               //smullyan_knights_knaves_normals
               {"upTo5sec/smullyan_knights_knaves_normals/smullyan_knights_knaves_normals"},

               //smullyan_knights_knaves_normals_bahava
               {"upTo5sec/smullyan_knights_knaves_normals_bahava/smullyan_knights_knaves_normals_bahava"},

               //smullyan_lion_and_unicorn
               {"upTo5sec/smullyan_lion_and_unicorn/smullyan_lion_and_unicorn"},

               //smullyan_portia
               {"upTo5sec/smullyan_portia/smullyan_portia"},

               //soccer_puzzle
               {"upTo5sec/soccer_puzzle/soccer_puzzle"},

               //social_golfers1
               {"upTo5sec/social_golfers1/social_golfers1"},

               //social_golfers2
               {"upTo5sec/social_golfers2/social_golfers2"},

               //soft_all_equal_ctr
               {"upTo5sec/soft_all_equal_ctr/soft_all_equal_ctr"},

               //soft_same_var
               {"upTo5sec/soft_same_var/soft_same_var"},

               //sokoban
               {"upTo5sec/sokoban/sokoban"},

               //solitaire_battleship
               {"upTo5sec/solitaire_battleship/solitaire_battleship"},

               //sonet_problem
               {"upTo5sec/sonet_problem/sonet_problem"},

               //sort_permutation
               {"upTo5sec/sort_permutation/sort_permutation"},

               //sortedness
               {"upTo5sec/sortedness/sortedness"},

               //spinning_disks
               {"upTo5sec/spinning_disks/spinning_disks"},

               //sportsScheduling
               {"upTo5sec/sportsScheduling/sportsScheduling"},

               {"upTo5sec/spp/spp"},

               //spreadsheet
               {"upTo5sec/spreadsheet/spreadsheet"},

               //spy_girls
               {"upTo5sec/spy_girls/spy_girls"},

               //squeens
               {"upTo5sec/squeens/squeens"},

               //stable_marriage
               {"upTo5sec/stable_marriage/stable_marriage"},

               //stamp_licking
               {"upTo5sec/stamp_licking/stamp_licking"},

               //steiner
               {"upTo5sec/steiner/steiner"},

               //stretch_circuit
               {"upTo5sec/stretch_circuit/stretch_circuit"},

               //stretch_path
               {"upTo5sec/stretch_path/stretch_path"},

               //strictly_decreasing
               {"upTo5sec/strictly_decreasing/strictly_decreasing"},

               //stuckey_assignment
               {"upTo5sec/stuckey_assignment/stuckey_assignment"},

               //stuckey_seesaw
               {"upTo5sec/stuckey_seesaw/stuckey_seesaw"},

               //students_and_languages
               {"upTo5sec/students_and_languages/students_and_languages"},

               //subsequence
               {"upTo5sec/subsequence/subsequence"},

               //subsequence_sum
               {"upTo5sec/subsequence_sum/subsequence_sum"},

               //subset_plus_2
               {"upTo5sec/subset_plus_2/subset_plus_2"},

               //subsets_100
               {"upTo5sec/subsets_100/subsets_100"},

               //successive_number_problem
               {"upTo5sec/successive_number_problem/successive_number_problem"},

               //sudoku_25x25_250
               {"upTo5sec/sudoku_25x25_250/sudoku_25x25_250"},

               //sudoku_gcc
               {"upTo5sec/sudoku_gcc/sudoku_gcc"},

               //sudoku_ip
               {"upTo5sec/sudoku_ip/sudoku_ip"},

               //sudoku_multi
               {"upTo5sec/sudoku_multi/sudoku_multi"},

               //sudoku_multi2
               {"upTo5sec/sudoku_multi2/sudoku_multi2"},

               //sudoku_pi
               {"upTo5sec/sudoku_pi/sudoku_pi"},

               //sudoku_pi_2008
               {"upTo5sec/sudoku_pi_2008/sudoku_pi_2008"},

               //sudoku_pi_2010
               {"upTo5sec/sudoku_pi_2010/sudoku_pi_2010"},

               //sudoku_pi_2011
               {"upTo5sec/sudoku_pi_2011/sudoku_pi_2011"},

               //sudoku_pi_day_2015
               {"upTo5sec/sudoku_pi_day_2015/sudoku_pi_day_2015"},

               //sudoku_pi_with_comments
               {"upTo5sec/sudoku_pi_with_comments/sudoku_pi_with_comments"},

               //sultans_children
               {"upTo5sec/sultans_children/sultans_children"},

               //sum_ctr
               {"upTo5sec/sum_ctr/sum_ctr"},

               //sum_first_and_last
               {"upTo5sec/sum_first_and_last/sum_first_and_last"},

               //sum_free
               {"upTo5sec/sum_free/sum_free"},

               //sum_of_next_natural_numbers
               {"upTo5sec/sum_of_next_natural_numbers/sum_of_next_natural_numbers"},

               //sum_of_weights_of_distinct_values
               {"upTo5sec/sum_of_weights_of_distinct_values/sum_of_weights_of_distinct_values"},

               //sum_set
               {"upTo5sec/sum_set/sum_set"},

               //sum_set
               {"upTo5sec/sum_sets/sum_sets"},

               //sum_to_100
               {"upTo5sec/sum_to_100/sum_to_100"},

               //sumbrero
               {"upTo5sec/sumbrero/sumbrero"},

               //survivor
               {"upTo5sec/survivor/survivor"},

               //survo_puzzle
               {"upTo5sec/survo_puzzle/survo_puzzle"},

               //symmetric
               {"upTo5sec/symmetric/symmetric"},

               //symmetric_alldifferent
               {"upTo5sec/symmetric_alldifferent/symmetric_alldifferent"},

               //symmetry_breaking
               {"upTo5sec/symmetry_breaking/symmetry_breaking"},

               //table_of_numbers
               {"upTo5sec/table_of_numbers/table_of_numbers"},

               //takuzu
               {"upTo5sec/takuzu/takuzu"},

               //talent
               {"upTo5sec/talent/talent"},

               //talisman_square
               {"upTo5sec/talisman_square/talisman_square"},

               //tank
               {"upTo5sec/tank/tank"},

               //teambuilding
               {"upTo5sec/teambuilding/teambuilding"},

               //temporal_reasoning
               {"upTo5sec/temporal_reasoning/temporal_reasoning"},

               //ten_statements
               {"upTo5sec/ten_statements/ten_statements"},

               //tennis_problem
               {"upTo5sec/tennis_problem/tennis_problem"},

               //tennis_tournament
               {"upTo5sec/tennis_tournament/tennis_tournament"},

               //the_bomb
               {"upTo5sec/the_bomb/the_bomb"},

               //the_family_puzzle
               {"upTo5sec/the_family_puzzle/the_family_puzzle"},

               //the_interns
               {"upTo5sec/the_interns/the_interns"},

               //thick_as_thieves
               {"upTo5sec/thick_as_thieves/thick_as_thieves"},

               //thirteen_link_chain_puzzle
               {"upTo5sec/thirteen_link_chain_puzzle/thirteen_link_chain_puzzle"},

               //thirteen_link_chain_puzzle2
               {"upTo5sec/thirteen_link_chain_puzzle2/thirteen_link_chain_puzzle2"},

               //thirteen_link_chain_puzzle3
               {"upTo5sec/thirteen_link_chain_puzzle3/thirteen_link_chain_puzzle3"},

               //three_digit
               {"upTo5sec/three_digit/three_digit"},

               //tickTackToe
               {"upTo5sec/tickTackToe/tickTackToe"},

               //tictactoe_avoidance
               {"upTo5sec/tictactoe_avoidance/tictactoe_avoidance"},

               //timeslots_for_songs
               {"upTo5sec/timeslots_for_songs/timeslots_for_songs"},

               //timetable
               {"upTo5sec/timetable/timetable"},

               //timpkin
               {"upTo5sec/timpkin/timpkin"},

               //transpose
               {"upTo5sec/transpose/transpose"},

               //trial1
               {"upTo5sec/trial1/trial1"},

               //trial2
               {"upTo5sec/trial2/trial2"},

               //trial3
               {"upTo5sec/trial3/trial3"},

               //trial4
               {"upTo5sec/trial4/trial4"},

               //trial5
               {"upTo5sec/trial5/trial5"},

               //trial6
               {"upTo5sec/trial6/trial6"},

               //trial12
               {"upTo5sec/trial12/trial12"},

               //triangles
               {"upTo5sec/triangles/triangles"},

               //tripuzzle1
               {"upTo5sec/tripuzzle1/tripuzzle1"},

               //tripuzzle2
               {"upTo5sec/tripuzzle2/tripuzzle2"},

               //tunapalooza
               {"upTo5sec/tunapalooza/tunapalooza"},

               //twelve
               {"upTo5sec/twelve/twelve"},

               //twelve_statements
               {"upTo5sec/twelve_statements/twelve_statements"},

               //twin
               {"upTo5sec/twin/twin"},

               //twin_letters
               {"upTo5sec/twin_letters/twin_letters"},

               //two_cube_calendar
               {"upTo5sec/two_cube_calendar/two_cube_calendar"},

               //two_dimensional_channels
               {"upTo5sec/two_dimensional_channels/two_dimensional_channels"},

               //uniform_dice
               {"upTo5sec/uniform_dice/uniform_dice"},

               //unique_set_puzzle
               {"upTo5sec/unique_set_puzzle/unique_set_puzzle"},

               //urban_planning
               {"upTo30sec/urban_planning/urban_planning"},

               //uzbekian_puzzle
               {"upTo5sec/uzbekian_puzzle/uzbekian_puzzle"},

               //vingt_cinq_cinq_trente
               {"upTo5sec/vingt_cinq_cinq_trente/vingt_cinq_cinq_trente"},

               //virtual_chess_tournament
               {"upTo5sec/virtual_chess_tournament/virtual_chess_tournament"},

               //tomography
               {"upTo5sec/tomography/tomography"},

               //tomography_n_colors
               {"upTo5sec/tomography_n_colors/tomography_n_colors"},

               //torn_number
               {"upTo5sec/torn_number/torn_number"},

               //tourist_site_competition
               {"upTo5sec/tourist_site_competition/tourist_site_competition"},

               //traffic_lights
               {"upTo5sec/traffic_lights/traffic_lights"},

               //traffic_lights_table
               {"upTo5sec/traffic_lights_table/traffic_lights_table"},

               //voltage_divider
               {"upTo5sec/voltage_divider/voltage_divider"},

               //war_or_peace
               {"upTo5sec/war_or_peace/war_or_peace"},

               //water_buckets1
               {"upTo5sec/water_buckets1/water_buckets1"},

               //wedding_optimal_chart
               {"upTo5sec/wedding_optimal_chart/wedding_optimal_chart"},

               //weighted_sum
               {"upTo5sec/weighted_sum/weighted_sum"},

               //were2
               {"upTo5sec/were2/were2"},

               //were4
               {"upTo5sec/were4/were4"},

               //who_killed_agatha
               {"upTo5sec/who_killed_agatha/who_killed_agatha"},

               //wijuko
               {"upTo5sec/wijuko/wijuko"},

               //wine_cask_puzzle
               {"upTo5sec/wine_cask_puzzle/wine_cask_puzzle"},

               //wiseman_problem_20131129
               {"upTo5sec/wiseman_problem_20131129/wiseman_problem_20131129"},

               //wolf_goat_cabbage_lp
               {"upTo5sec/wolf_goat_cabbage_lp/wolf_goat_cabbage_lp"},

               //word_golf
               //Warning: Not implemented indomain method "indomain"; used indomain_min
               {"upTo5sec/word_golf/word_golf"},

               //word_square
               {"upTo5sec/word_square/word_square"},

               //young_tableaux_stack_overflow
               {"upTo5sec/young_tableaux_stack_overflow/young_tableaux_stack_overflow"},

               //zebra_inverse
               {"upTo5sec/zebra_inverse/zebra_inverse"},

               //zebra_ip
               {"upTo5sec/zebra_ip/zebra_ip"},

               //rotation2
               {"upTo5sec/rotation2/rotation2"},

               //state_name_puzzle
               {"upTo1min/state_name_puzzle/state_name_puzzle"},

                        //numberlink
               {"upTo5sec/numberlink/numberlink1"},
               {"upTo5sec/numberlink/numberlink3"},
               {"upTo5sec/numberlink/numberlink7"},

               //mceverywhere
               {"upTo5min/mceverywhere/mceverywhere"},

               //tsp_circuit
               {"upTo1hour/tsp_circuit/tsp_circuit"},

               //tsptw
               {"upTo5min/tsptw/tsptw"},

               //magic_sequence4
               {"upTo5min//magic_sequence4/magic_sequence4"},

               //portfolio_optimization2
               {"upTo10min/portfolio_optimization2/portfolio_optimization2"},

               //product_ctr
               {"upTo5sec/product_ctr/product_ctr"},

               //scheduling_speakers_optimize3
               {"upTo5min/scheduling_speakers_optimize3/scheduling_speakers_optimize3"},

               //touching_numbers
               {"upTo5min/touching_numbers/touching_numbers"},

               //cube_sum
               {"upTo5sec/cube_sum/cube_sum"},

               //cumulative_test
               {"upTo5sec/cumulative_test/cumulative_test"},

               //cumulative_test_mats_carlsson
               {"upTo5sec/cumulative_test_mats_carlsson/cumulative_test_mats_carlsson"},


               //assign
               {"upTo5sec/assign/assign"},

               //aust_colord
               {"upTo5sec/aust_colord/aust_colord"},

               //missing_solution
               {"upTo5sec/missing_solution/missing_solution"}, //=====UNSATISFIABLE=====

               //carpet_cutting
               {"upTo5sec/carpet_cutting/carpet_cutting"},

               //carpet_cutting_geost
               {"upTo5sec/carpet_cutting_geost/carpet_cutting_geost"},

               //alpha
               {"upTo5sec/alpha/alpha"},

               //amaze
               {"upTo5sec/amaze/2012-03-07"},
               {"upTo5sec/amaze/2012-03-09"},
               {"upTo5sec/amaze/2012-03-14"},
               {"upTo5min/amaze/2012-03-15"},
               {"upTo5min/amaze/2012-03-19"},
               {"upTo5sec/amaze/2012-03-29"},
               {"upTo5sec/amaze/2012-04-03"},
               {"upTo5sec/amaze/2012-04-05"},
               {"upTo5sec/amaze/2012-04-12"},
               {"upTo5sec/amaze/2012-04-13"},
               {"upTo5sec/amaze/2012-04-16"},
               {"upTo5sec/amaze/2012-04-19"},
               {"upTo5sec/amaze/2012-04-20"},
               {"upTo5sec/amaze/2012-04-23"},

               //cell_block
               {"upTo5sec/cell_block/cell_block"},

               //cell_block_func
               {"upTo5sec/cell_block/cell_block_func"},

               //compatible_assignment
               {"upTo5sec/compatible_assignment/compatible_assignment"},

               //compatible_assignment_opt
               {"upTo5sec/compatible_assignment/compatible_assignment_opt"},


               //constrained_connected
               {"upTo1hour/constrained_connected/constrained_connected"},


               //doublechannel
               {"upTo5sec/doublechannel/channel1"},
               {"upTo5sec/doublechannel/channel2"},


                //areas
                {"upTo5sec/areas/2_2_1"},
                {"upTo5sec/areas/3_3_3"},
                {"upTo5sec/areas/3_3_5"},
                {"upTo5sec/areas/5_5_9"},

//*************************************************************

                //bibd
                {"upTo5sec/bibd/03_03_01"},
                {"upTo5sec/bibd/04_02_01"},
                {"upTo5sec/bibd/06_03_02"},
                {"upTo5sec/bibd/07_03_01"},
                {"upTo5sec/bibd/07_03_02"},
                {"upTo5sec/bibd/08_04_03"},
                {"upTo5sec/bibd/09_03_01"},
                {"upTo5sec/bibd/11_05_02"},
                {"upTo5sec/bibd/13_03_01"},
                {"upTo5sec/bibd/15_03_01"},
                {"upTo5sec/bibd/15_07_03"},
                {"upTo5sec/bibd/16_04_01"},
                {"upTo5sec/bibd/19_03_01"},


                //crazy_sets
                {"upTo5sec/crazy_sets/crazy_sets"},
                {"upTo5sec/crazy_sets/crazy_sets_global"},

                //flattening
                {"upTo5sec/flattening/flattening1"},
                {"upTo5sec/flattening/flattening2"},
                {"upTo5sec/flattening/flattening3"},
                {"upTo5sec/flattening/flattening4"},
                {"upTo5sec/flattening/flattening5"},
                {"upTo5sec/flattening/flattening6"},
                {"upTo5sec/flattening/flattening7"},
                {"upTo5sec/flattening/flattening8"},
                {"upTo5sec/flattening/flattening9"},
                {"upTo5sec/flattening/flattening10"},
                {"upTo5sec/flattening/flattening11"},
                //upTo5sec/flattening/flattening12.fzn
                //%%	java.lang.ArithmeticException: Overflow occurred from int 50000000 * 50000000
                //{"upTo5sec/flattening/flattening12"},
                //%%	java.lang.ArithmeticException: Overflow occurred from int 50000000 * 50000000
                //{"upTo5sec/flattening/flattening13"},
                {"upTo5sec/flattening/flattening14"},

                //jobshop
                {"upTo5sec/jobshop/jobshop"},
                {"upTo5sec/jobshop/jobshop2"},
                {"upTo5sec/jobshop/jobshop3"},

                //ltsp
                {"upTo5sec/ltsp/ltsp"},

                //loan
                {"upTo5sec/loan/loan1"},
                {"upTo5sec/loan/loan2"},

                //mip
                //java.lang.AssertionError: Request for a value of not grounded variable -X_INTRODUCED_7::{-5.570655048359189E-11..-0.0}
                // {"test/mip/mip1"},
                //java.lang.AssertionError: Request for a value of not grounded variable -X_INTRODUCED_1::{0.2156132152879184..0.21561321530379057}
                // {"test/mip/mip2"},
                //java.lang.IndexOutOfBoundsException: Index: 0, Size: 0
                // {"test/mip/mip3"},
                //java.lang.IndexOutOfBoundsException: Index: 0, Size: 0
                // {"test/mip/mip4"},
                //java.lang.IndexOutOfBoundsException: Index: 0, Size: 0
                // {"test/mip/mip5"},

                //nurses
                {"upTo5sec/nurses/nurses_let"},
                {"upTo5sec/nurses/nurses"},

                //photo
                {"upTo5sec/photo/photo"},

                //simple-prod-planning
                {"upTo5sec/simple-prod-planning/simple-prod-planning"},

                //project_scheduling
                {"upTo5sec/project_scheduling/project_scheduling"},
                {"upTo5sec/project_scheduling/project_scheduling_nonoverlap"},


                //array_quest
                {"upTo5sec/array_quest/array_quest"},

                //graph
                {"upTo5sec/graph/graph"},

                //missingsolution
                {"upTo5sec/missingsolution/missingsolution"},

                //myabs
                {"upTo5sec/myabs/myabs"},

                //mydiv
                {"upTo5sec/mydiv/mydiv"},

                //toomany
                {"upTo5sec/toomany/toomany"},

                //eq
                {"upTo5sec/eq/eq20"},

                //fastfood

                  {"upTo5sec/fastfood/ff1"},
                  {"upTo5sec/fastfood/ff2"},
                  {"upTo30sec/fastfood/ff3"},
                  {"upTo5sec/fastfood/ff4"},
                  {"upTo5sec/fastfood/ff5"},
                  {"upTo5sec/fastfood/ff6"},
                  {"upTo5sec/fastfood/ff7"},
                  {"upTo5sec/fastfood/ff8"},
                  {"upTo5sec/fastfood/ff9"},
                  {"upTo5sec/fastfood/ff10"},
                  {"upTo30sec/fastfood/ff11"},
                  {"upTo5sec/fastfood/ff12"},
                  {"upTo5sec/fastfood/ff13"},
                  {"upTo5sec/fastfood/ff14"},
                  {"upTo5sec/fastfood/ff15"},
                  {"upTo5sec/fastfood/ff16"},
                  {"upTo5sec/fastfood/ff17"},
                  {"upTo5sec/fastfood/ff18"},
                  {"upTo5sec/fastfood/ff19"},
                  {"upTo5sec/fastfood/ff20"},
                  {"upTo30sec/fastfood/ff21"},
                  {"upTo5sec/fastfood/ff22"},
                  {"upTo5sec/fastfood/ff23"},
                  {"upTo5sec/fastfood/ff24"},
                  {"upTo5sec/fastfood/ff25"},
                  {"upTo5sec/fastfood/ff26"},
                  {"upTo5sec/fastfood/ff27"},
                  {"upTo5sec/fastfood/ff28"},
                  {"upTo5sec/fastfood/ff29"},
                  {"upTo5sec/fastfood/ff30"},
                  {"upTo5sec/fastfood/ff31"},
                  {"upTo5sec/fastfood/ff32"},
                  {"upTo5sec/fastfood/ff33"},
                  {"upTo5sec/fastfood/ff34"},
                  {"upTo5sec/fastfood/ff35"},
                  {"upTo5sec/fastfood/ff36"},
                  {"upTo5sec/fastfood/ff37"},
                  {"upTo5sec/fastfood/ff38"},
                  {"upTo5sec/fastfood/ff39"},
                  {"upTo5sec/fastfood/ff40"},
                  {"upTo5sec/fastfood/ff41"},
                  {"upTo5sec/fastfood/ff42"},
                  {"upTo5sec/fastfood/ff43"},
                  {"upTo5sec/fastfood/ff44"},
                  {"upTo5sec/fastfood/ff45"},
                  {"upTo5sec/fastfood/ff46"},
                  {"upTo5sec/fastfood/ff47"},
                  {"upTo5sec/fastfood/ff48"},
                  {"upTo5sec/fastfood/ff49"},
                  {"upTo5sec/fastfood/ff50"},
                  {"upTo5sec/fastfood/ff51"},
                  {"upTo5sec/fastfood/ff52"},
                  {"upTo5sec/fastfood/ff53"},
                  {"upTo5sec/fastfood/ff54"},
                  {"upTo5sec/fastfood/ff55"},
                  {"upTo30sec/fastfood/ff56"},
                  {"upTo5sec/fastfood/ff57"},
                  {"upTo5min/fastfood/ff58"},
                  {"upTo1min/fastfood/ff59"},
                  {"upTo1min/fastfood/ff60"},
                  {"upTo1min/fastfood/ff61"},
                  {"upTo1min/fastfood/ff62"},
                  {"upTo30sec/fastfood/ff63"},
                  {"upTo30sec/fastfood/ff64"},
                  {"upTo30sec/fastfood/ff65"},
                  {"upTo5sec/fastfood/ff66"},
                  {"upTo5sec/fastfood/ff67"},
                  {"upTo5sec/fastfood/ff68"},
                  {"upTo5sec/fastfood/ff69"},
                  {"upTo5sec/fastfood/ff70"},
                  {"upTo5sec/fastfood/ff71"},
                  {"upTo5sec/fastfood/ff72"},
                  {"upTo5sec/fastfood/ff73"},
                  {"upTo30sec/fastfood/ff74"},
                  {"upTo30sec/fastfood/ff75"},
                  {"upTo30sec/fastfood/ff76"},
                  {"upTo5sec/fastfood/ff77"},
                  {"upTo5sec/fastfood/ff78"},
                  {"upTo5sec/fastfood/ff79"},
                  {"upTo5sec/fastfood/ff80"},
                  {"upTo5sec/fastfood/ff81"},
                  {"upTo5sec/fastfood/ff82"},
                  {"upTo5sec/fastfood/ff83"},
                  {"upTo5sec/fastfood/ff84"},
                  {"upTo5sec/fastfood/ff85"},
                  {"upTo5sec/fastfood/ff86"},
                  {"upTo5sec/fastfood/ff87"},
                  {"upTo5sec/fastfood/ff88"},
                  {"upTo5sec/fastfood/ff89"},




                //bacp
//                {"test/bacp/bacp-1"},
                //{"upTo5sec/bacp/bacp-2"},
                //timeout{"test/bacp/bacp-3"},
                //java.lang.IndexOutOfBoundsException: Index: 0, Size: 0{"test/bacp/bacp-4"},
                //timeout{"test/bacp/bacp-5"},
                //java.lang.IndexOutOfBoundsException: Index: 0, Size: 0{"test/bacp/bacp-6"},
                //java.lang.IndexOutOfBoundsException: Index: 0, Size: 0{"test/bacp/bacp-7"},
                //timeout{"test/bacp/bacp-8"},
                //timeout{"test/bacp/bacp-9"},
                {"test/bacp/bacp-10"},
                //{"upTo10min/bacp/bacp-10"},



                //timeout{"test/bacp/bacp-11"},
                //java.lang.IndexOutOfBoundsException: Index: 0, Size: 0
                // {"test/bacp/bacp-12"},
                //java.lang.IndexOutOfBoundsException: Index: 0, Size: 0
                // {"test/bacp/bacp-13"},
                //java.lang.IndexOutOfBoundsException: Index: 0, Size: 0
                // {"test/bacp/bacp-14"},
                //java.lang.IndexOutOfBoundsException: Index: 0, Size: 0
                // {"test/bacp/bacp-15"},
                //java.lang.IndexOutOfBoundsException: Index: 0, Size: 0
                // {"test/bacp/bacp-16"},
                //java.lang.IndexOutOfBoundsException: Index: 0, Size: 0
                // {"test/bacp/bacp-17"},
                //java.lang.IndexOutOfBoundsException: Index: 0, Size: 0
                // {"test/bacp/bacp-18"},
                //java.lang.IndexOutOfBoundsException: Index: 0, Size: 0
                // {"test/bacp/bacp-19"},
                //java.lang.IndexOutOfBoundsException: Index: 0, Size: 0
                // {"test/bacp/bacp-20"},
                //java.lang.IndexOutOfBoundsException: Index: 0, Size: 0
                // {"test/bacp/bacp-21"},
                //java.lang.IndexOutOfBoundsException: Index: 0, Size: 0
                // {"test/bacp/bacp-22"},
                //java.lang.IndexOutOfBoundsException: Index: 0, Size: 0
                // {"test/bacp/bacp-23"},
                //java.lang.IndexOutOfBoundsException: Index: 0, Size: 0
                // {"test/bacp/bacp-24"},
                //java.lang.IndexOutOfBoundsException: Index: 0, Size: 0
                // {"test/bacp/bacp-25"},
                //java.lang.IndexOutOfBoundsException: Index: 0, Size: 0
                // {"test/bacp/bacp-26"},
                //java.lang.IndexOutOfBoundsException: Index: 0, Size: 0
                // {"test/bacp/bacp-27"},
                //java.lang.IndexOutOfBoundsException: Index: 0, Size: 0
                // {"test/bacp/bacp-28"},

                //black-hole
                //java.lang.IndexOutOfBoundsException: Index: 0, Size: 0
                // {"test/black-hole/0"},
                //java.lang.IndexOutOfBoundsException: Index: 0, Size: 0
                //timeout{"test/black-hole/1"},
                {"test/black-hole/2"},
                //java.lang.IndexOutOfBoundsException: Index: 0, Size: 0{"test/black-hole/3"},
                //timeout{"test/black-hole/4"},
                //java.lang.IndexOutOfBoundsException: Index: 0, Size: 0{"test/black-hole/5"},
                //java.lang.IndexOutOfBoundsException: Index: 0, Size: 0{"test/black-hole/6"},
                //java.lang.IndexOutOfBoundsException: Index: 0, Size: 0{"test/black-hole/7"},
                //java.lang.IndexOutOfBoundsException: Index: 0, Size: 0{"test/black-hole/8"},
                //java.lang.IndexOutOfBoundsException: Index: 0, Size: 0{"test/black-hole/9"},
                //java.lang.IndexOutOfBoundsException: Index: 0, Size: 0{"test/black-hole/10"},
                //timeout{"test/black-hole/11"},
                //java.lang.IndexOutOfBoundsException: Index: 0, Size: 0{"test/black-hole/12"},
                //java.lang.IndexOutOfBoundsException: Index: 0, Size: 0{"test/black-hole/13"},
                //timeout{"test/black-hole/14"},

               {"test/black-hole/15"},

                {"test/black-hole/16"},
                {"test/black-hole/17"},
                {"test/black-hole/18"},
                {"test/black-hole/19"},
                {"test/black-hole/20"},

                //bus_scheduling
                {"test/bus_scheduling/c1"},
                {"test/bus_scheduling/c1a"},
                {"test/bus_scheduling/c2"},
                {"test/bus_scheduling/r1"},
                {"test/bus_scheduling/r1a"},
                {"test/bus_scheduling/r2"},
                {"test/bus_scheduling/r3"},
                {"test/bus_scheduling/r4"},
                {"test/bus_scheduling/r5"},
                {"test/bus_scheduling/r5a"},
                {"test/bus_scheduling/t2"},

                //cargo
                {"test/cargo/challenge04_1s_626"},
                {"test/cargo/challenge05_1s_954"},
                {"test/cargo/challenge07_1s_133"},
                {"test/cargo/challenge08_222f_3475"},
                {"test/cargo/challenge10_15966f_2060"},


                //carpet-cutting
                {"test/carpet-cutting/mzn_rnd_test.01"},
                {"test/carpet-cutting/mzn_rnd_test.02"},
                {"test/carpet-cutting/mzn_rnd_test.03"},
                {"test/carpet-cutting/mzn_rnd_test.04"},
                {"test/carpet-cutting/mzn_rnd_test.05"},
                {"test/carpet-cutting/mzn_rnd_test.06"},
                {"test/carpet-cutting/mzn_rnd_test.07"},
                {"test/carpet-cutting/mzn_rnd_test.08"},
                {"test/carpet-cutting/mzn_rnd_test.09"},
                {"test/carpet-cutting/mzn_rnd_test.10"},
                {"test/carpet-cutting/mzn_rnd_test.11"},
                {"test/carpet-cutting/mzn_rnd_test.12"},
                {"test/carpet-cutting/mzn_rnd_test.13"},
                {"test/carpet-cutting/mzn_rnd_test.14"},
                {"test/carpet-cutting/mzn_rnd_test.15"},
                {"test/carpet-cutting/mzn_rnd_test.16"},
                {"test/carpet-cutting/mzn_rnd_test.17"},
                {"test/carpet-cutting/mzn_rnd_test.18"},
                {"test/carpet-cutting/mzn_rnd_test.19"},
                {"test/carpet-cutting/mzn_rnd_test.20"},

<<<<<<< HEAD
//                //cutstock
//                {"test/cutstock/small_test0"},
//                {"test/cutstock/type01_TEST1"},
//                {"test/cutstock/type01_TEST2"},
//                {"test/cutstock/type01_TEST3"},
//                {"test/cutstock/type01_TEST4"},
//                {"test/cutstock/type01_TEST5"},
//                {"test/cutstock/type01_TEST6"},
//                {"test/cutstock/type01_TEST7"},
//                {"test/cutstock/type01_TEST8"},
//                {"test/cutstock/type01_TEST10"},
//                {"test/cutstock/type02_TEST1"},
//                {"test/cutstock/type02_TEST2"},
//                {"test/cutstock/type02_TEST3"},
//                {"test/cutstock/type02_TEST4"},
//                {"test/cutstock/type02_TEST5"},
//                {"test/cutstock/type02_TEST6"},
//                {"test/cutstock/type02_TEST7"},
//                {"test/cutstock/type02_TEST8"},
//                {"test/cutstock/type02_TEST9"},
//                {"test/cutstock/type02_TEST10"},
//                {"test/cutstock/type03_TEST1"},
//                {"test/cutstock/type03_TEST2"},
//                {"test/cutstock/type03_TEST3"},
//                {"test/cutstock/type03_TEST4"},
//                {"test/cutstock/type03_TEST5"},
//                {"test/cutstock/type03_TEST6"},
//                {"test/cutstock/type03_TEST7"},
//                {"test/cutstock/type03_TEST8"},
//                {"test/cutstock/type03_TEST9"},
//                {"test/cutstock/type03_TEST10"},
//                {"test/cutstock/type04_TEST1"},
//                {"test/cutstock/type04_TEST2"},
//                {"test/cutstock/type04_TEST3"},
//                {"test/cutstock/type04_TEST4"},
//                {"test/cutstock/type04_TEST5"},
//                {"test/cutstock/type04_TEST6"},
//                {"test/cutstock/type04_TEST7"},
//                {"test/cutstock/type04_TEST8"},
//                {"test/cutstock/type04_TEST9"},
//                {"test/cutstock/type04_TEST10"},
//                {"test/cutstock/type07_TEST1"},
//                {"test/cutstock/type07_TEST2"},
//                {"test/cutstock/type07_TEST3"},
//                {"test/cutstock/type07_TEST4"},
//                {"test/cutstock/type07_TEST5"},
//                {"test/cutstock/type07_TEST7"},
//                {"test/cutstock/type07_TEST8"},
//                {"test/cutstock/type07_TEST9"},
//                {"test/cutstock/type07_TEST10"},
//                {"test/cutstock/type08_TEST1"},
//                {"test/cutstock/type08_TEST2"},
//                {"test/cutstock/type08_TEST3"},
//                {"test/cutstock/type08_TEST4"},
//                {"test/cutstock/type08_TEST5"},
//                {"test/cutstock/type08_TEST6"},
//                {"test/cutstock/type08_TEST7"},
//                {"test/cutstock/type08_TEST8"},
//                {"test/cutstock/type08_TEST9"},
//                {"test/cutstock/type08_TEST10"},
//                {"test/cutstock/type09_TEST1"},
//                {"test/cutstock/type09_TEST2"},
//                {"test/cutstock/type09_TEST3"},
//                {"test/cutstock/type09_TEST4"},
//                {"test/cutstock/type09_TEST5"},
//                {"test/cutstock/type09_TEST6"},
//                {"test/cutstock/type09_TEST7"},
//                {"test/cutstock/type09_TEST8"},
//                {"test/cutstock/type09_TEST9"},
//                {"test/cutstock/type09_TEST10"},
//                {"test/cutstock/type10_TEST1"},
//                {"test/cutstock/type10_TEST2"},
//                {"test/cutstock/type10_TEST3"},
//                {"test/cutstock/type10_TEST4"},
//                {"test/cutstock/type10_TEST5"},
//                {"test/cutstock/type10_TEST6"},
//                {"test/cutstock/type10_TEST7"},
//                {"test/cutstock/type10_TEST8"},
//                {"test/cutstock/type10_TEST9"},
//                {"test/cutstock/type10_TEST10"},
//                {"test/cutstock/type13_TEST1"},
//                {"test/cutstock/type13_TEST2"},
//                {"test/cutstock/type13_TEST3"},
//                {"test/cutstock/type13_TEST4"},
//                {"test/cutstock/type13_TEST5"},
//                {"test/cutstock/type13_TEST6"},
//                {"test/cutstock/type13_TEST7"},
//                {"test/cutstock/type13_TEST8"},
//                {"test/cutstock/type13_TEST9"},
//                {"test/cutstock/type13_TEST10"},
//                {"test/cutstock/type14_TEST1"},
//                {"test/cutstock/type14_TEST2"},
//                {"test/cutstock/type14_TEST3"},
//                {"test/cutstock/type14_TEST4"},
//                {"test/cutstock/type14_TEST5"},
//                {"test/cutstock/type14_TEST6"},
//                {"test/cutstock/type14_TEST7"},
//                {"test/cutstock/type14_TEST8"},
//                {"test/cutstock/type14_TEST9"},
//                {"test/cutstock/type14_TEST10"},
//                {"test/cutstock/type15_TEST1"},
//                {"test/cutstock/type15_TEST2"},
//                {"test/cutstock/type15_TEST3"},
//                {"test/cutstock/type15_TEST4"},
//                {"test/cutstock/type15_TEST5"},
//                {"test/cutstock/type15_TEST6"},
//                {"test/cutstock/type15_TEST7"},
//                {"test/cutstock/type15_TEST8"},
//                {"test/cutstock/type15_TEST9"},
//                {"test/cutstock/type15_TEST10"},
//                {"test/cutstock/type16_TEST1"},
//                {"test/cutstock/type16_TEST2"},
//                {"test/cutstock/type16_TEST3"},
//                {"test/cutstock/type16_TEST4"},
//                {"test/cutstock/type16_TEST5"},
//                {"test/cutstock/type16_TEST6"},
//                {"test/cutstock/type16_TEST7"},
//                {"test/cutstock/type16_TEST8"},
<<<<<<< HEAD
=======
                //cutstock
                {"test/cutstock/small_test0"},
                //timeout{"test/cutstock/type01_TEST1"},
                //timeout{"test/cutstock/type01_TEST2"},
                {"test/cutstock/type01_TEST3"},
                {"test/cutstock/type01_TEST4"},
                {"test/cutstock/type01_TEST5"},
                {"test/cutstock/type01_TEST6"},
                {"test/cutstock/type01_TEST7"},
                {"test/cutstock/type01_TEST8"},
                {"test/cutstock/type01_TEST10"},
                {"test/cutstock/type02_TEST1"},
                {"test/cutstock/type02_TEST2"},
                {"test/cutstock/type02_TEST3"},
                {"test/cutstock/type02_TEST4"},
                {"test/cutstock/type02_TEST5"},
                {"test/cutstock/type02_TEST6"},
                {"test/cutstock/type02_TEST7"},
                {"test/cutstock/type02_TEST8"},
                {"test/cutstock/type02_TEST9"},
                {"test/cutstock/type02_TEST10"},
                {"test/cutstock/type03_TEST1"},
                {"test/cutstock/type03_TEST2"},
                {"test/cutstock/type03_TEST3"},
                {"test/cutstock/type03_TEST4"},
                {"test/cutstock/type03_TEST5"},
                {"test/cutstock/type03_TEST6"},
                {"test/cutstock/type03_TEST7"},
                {"test/cutstock/type03_TEST8"},
                {"test/cutstock/type03_TEST9"},
                {"test/cutstock/type03_TEST10"},
                {"test/cutstock/type04_TEST1"},
                {"test/cutstock/type04_TEST2"},
                {"test/cutstock/type04_TEST3"},
                {"test/cutstock/type04_TEST4"},
                {"test/cutstock/type04_TEST5"},
                {"test/cutstock/type04_TEST6"},
                {"test/cutstock/type04_TEST7"},
                {"test/cutstock/type04_TEST8"},
                {"test/cutstock/type04_TEST9"},
                {"test/cutstock/type04_TEST10"},
                {"test/cutstock/type07_TEST1"},
                {"test/cutstock/type07_TEST2"},
                {"test/cutstock/type07_TEST3"},
                {"test/cutstock/type07_TEST4"},
                {"test/cutstock/type07_TEST5"},
                {"test/cutstock/type07_TEST7"},
                {"test/cutstock/type07_TEST8"},
                {"test/cutstock/type07_TEST9"},
                {"test/cutstock/type07_TEST10"},
                {"test/cutstock/type08_TEST1"},
                {"test/cutstock/type08_TEST2"},
                {"test/cutstock/type08_TEST3"},
                {"test/cutstock/type08_TEST4"},
                {"test/cutstock/type08_TEST5"},
                {"test/cutstock/type08_TEST6"},
                {"test/cutstock/type08_TEST7"},
                {"test/cutstock/type08_TEST8"},
                {"test/cutstock/type08_TEST9"},
                {"test/cutstock/type08_TEST10"},
                {"test/cutstock/type09_TEST1"},
                {"test/cutstock/type09_TEST2"},
                {"test/cutstock/type09_TEST3"},
                {"test/cutstock/type09_TEST4"},
                {"test/cutstock/type09_TEST5"},
                {"test/cutstock/type09_TEST6"},
                {"test/cutstock/type09_TEST7"},
                {"test/cutstock/type09_TEST8"},
                {"test/cutstock/type09_TEST9"},
                {"test/cutstock/type09_TEST10"},
                {"test/cutstock/type10_TEST1"},
                {"test/cutstock/type10_TEST2"},
                {"test/cutstock/type10_TEST3"},
                {"test/cutstock/type10_TEST4"},
                {"test/cutstock/type10_TEST5"},
                {"test/cutstock/type10_TEST6"},
                {"test/cutstock/type10_TEST7"},
                {"test/cutstock/type10_TEST8"},
                {"test/cutstock/type10_TEST9"},
                {"test/cutstock/type10_TEST10"},
                {"test/cutstock/type13_TEST1"},
                {"test/cutstock/type13_TEST2"},
                {"test/cutstock/type13_TEST3"},
                {"test/cutstock/type13_TEST4"},
                {"test/cutstock/type13_TEST5"},
                {"test/cutstock/type13_TEST6"},
                {"test/cutstock/type13_TEST7"},
                {"test/cutstock/type13_TEST8"},
                {"test/cutstock/type13_TEST9"},
                {"test/cutstock/type13_TEST10"},
                {"test/cutstock/type14_TEST1"},
                {"test/cutstock/type14_TEST2"},
                {"test/cutstock/type14_TEST3"},
                {"test/cutstock/type14_TEST4"},
                {"test/cutstock/type14_TEST5"},
                {"test/cutstock/type14_TEST6"},
                {"test/cutstock/type14_TEST7"},
                {"test/cutstock/type14_TEST8"},
                {"test/cutstock/type14_TEST9"},
                {"test/cutstock/type14_TEST10"},
                {"test/cutstock/type15_TEST1"},
                {"test/cutstock/type15_TEST2"},
                {"test/cutstock/type15_TEST3"},
                {"test/cutstock/type15_TEST4"},
                {"test/cutstock/type15_TEST5"},
                {"test/cutstock/type15_TEST6"},
                {"test/cutstock/type15_TEST7"},
                {"test/cutstock/type15_TEST8"},
                {"test/cutstock/type15_TEST9"},
                {"test/cutstock/type15_TEST10"},
                {"test/cutstock/type16_TEST1"},
                {"test/cutstock/type16_TEST2"},
                {"test/cutstock/type16_TEST3"},
                {"test/cutstock/type16_TEST4"},
                {"test/cutstock/type16_TEST5"},
                {"test/cutstock/type16_TEST6"},
                {"test/cutstock/type16_TEST7"},
                {"test/cutstock/type16_TEST8"},
>>>>>>> c7661b2... testy


                //table_example
                //%% Out of memory error; consider option -Xmx... for JVM
                //{"test/table_example/table_example"},



                //toy_problem
                //%% Stack overflow exception error; consider option -Xss... for JVM
                //{"test/toy_problem/toy_problem"},




                //evilshop
                 {"test/evilshop/js-brs2-5"},
                 {"test/evilshop/js-brs2-6"},
                 {"test/evilshop/js-brs2-7"},
                 {"test/evilshop/js-ges1-4"},
                 {"test/evilshop/js-ges1-5"},
                 {"test/evilshop/js-setf1-7"},
                 {"test/evilshop/js-setf1-8"},
                 {"test/evilshop/js-setf1-10"},
                 {"test/evilshop/js-setf3-7"},
                 {"test/evilshop/js-setf3-8"},
                 {"test/evilshop/js-setf3-10"},
                 {"test/evilshop/js-setg2-5"},
                 {"test/evilshop/js-setg2-6"},
                 {"test/evilshop/js-setg2-7"},
                 {"test/evilshop/js-setg2-10"},


<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD


=======
                //filters
                 {"test/filters/ ewf_4_3"},
                 {"test/filters/ fir16_1_3"},
                 {"test/filters/ar_1_1"},
                 {"test/filters/ar_1_2"},
                 {"test/filters/ar_1_3"},
                 {"test/filters/ar_2_3"},
                 {"test/filters/dct_1_1"},
                 {"test/filters/dct_1_2"},
                 {"test/filters/dct_2_2"},
                 {"test/filters/dct_2_3"},
                 {"test/filters/dct_3_3"},
                 {"test/filters/dct_3_4"},
                 {"test/filters/dfq_1_1"},
                 {"test/filters/ewf_1_1"},
                 {"test/filters/ewf_2_1"},
                 {"test/filters/ewf_2_2"},
                 {"test/filters/fir16_1_1"},
                 {"test/filters/fir16_1_2"},
                 {"test/filters/fir16_1_3"},
                 {"test/filters/fir_1_1"},
                 {"test/filters/fir_1_2"},
                 {"test/filters/fir_2_2"},
                 {"test/filters/fir_2_3"},

                 //flexible-jobshop
                 {"test/flexible-jobshop/easy01"},
                 {"test/flexible-jobshop/hard19"},
                 {"test/flexible-jobshop/med04"},
                 {"test/flexible-jobshop/med10"},

                //ghoulomb
                 {"test/ghoulomb/3-3-3"},
                 {"test/ghoulomb/3-4-5"},
                 {"test/ghoulomb/3-4-6"},
                 {"test/ghoulomb/4-9-10"},
                 {"test/ghoulomb/4-9-12"},
                 {"test/ghoulomb/4-9-14"},
                 {"test/ghoulomb/3-7-16"},
                 {"test/ghoulomb/4-7-16"},
                 {"test/ghoulomb/3-8-16"},
                 {"test/ghoulomb/4-8-16"},
                 {"test/ghoulomb/3-9-16"},
                 {"test/ghoulomb/4-9-16"},
                 {"test/ghoulomb/3-10-16"},
                 {"test/ghoulomb/4-10-16"},
                 {"test/ghoulomb/4-9-18"},
                 {"test/ghoulomb/3-7-20"},
                 {"test/ghoulomb/4-7-20"},
                 {"test/ghoulomb/3-8-20"},
                 {"test/ghoulomb/4-8-20"},
                 {"test/ghoulomb/3-9-20"},
                 {"test/ghoulomb/4-9-20"},
                 {"test/ghoulomb/3-10-20"},

                //nonogram
                 {"test/nonogram/non_awful_1"},
                 {"test/nonogram/non_awful_2"},
                 {"test/nonogram/non_awful_3"},
                 {"test/nonogram/non_awful_5"},
                 {"test/nonogram/non_fast_1"},
                 {"test/nonogram/non_fast_2"},
                 {"test/nonogram/non_fast_3"},
                 {"test/nonogram/non_fast_4"},
                 {"test/nonogram/non_fast_5"},
                 {"test/nonogram/non_fast_6"},
                 {"test/nonogram/non_fast_7"},
                 {"test/nonogram/non_fast_8"},
                 {"test/nonogram/non_fast_9"},
                 {"test/nonogram/non_fast_10"},
                 {"test/nonogram/non_fast_11"},
                 {"test/nonogram/non_med_1"},
                 {"test/nonogram/non_med_2"},
                 {"test/nonogram/non_med_3"},
                 {"test/nonogram/non_med_4"},
>>>>>>> 56c19f3... test



=======
>>>>>>> 2ce0b8d... testy
=======
                {}
>>>>>>> 1ff724f... test
=======
>>>>>>> c7661b2... testy

                {}


                //golomb
                 {"test/golomb/03"},
                 {"test/golomb/04"},
                 {"test/golomb/05"},
                 {"test/golomb/06"},
                 {"test/golomb/07"},
                 {"test/golomb/08"},
                 {"test/golomb/09"},
                 {"test/golomb/10"},
                 {"test/golomb/11"},
                 {"test/golomb/12"},

                //java-routing
                 {"test/java-routing/trip_6_3"},
                 {"test/java-routing/trip_7_1"},
                 {"test/java-routing/trip_7_2"},
                 {"test/java-routing/trip_8_1"},
                 {"test/java-routing/trip_8_5"},

                //kakuro
                 {"test/kakuro/kakuro_6_6_easy"},
                 {"test/kakuro/kakuro_6_6_hard"},
                 {"test/kakuro/kakuro_8_8_easy"},
                 {"test/kakuro/kakuro_8_8_hard"},
                 {"test/kakuro/kakuro_8_8_super"},

                //rcpsp-max
                 {"test/rcpsp-max/psp_d_244"},
                 {"test/rcpsp-max/psp_j10_33"},
                 {"test/rcpsp-max/psp_d_301"},
                 {"test/rcpsp-max/psp_ubo100_22"},
                 {"test/rcpsp-max/psp_j30_244"},
                 {"test/rcpsp-max/psp_j30_169"},
                 {"test/rcpsp-max/psp_j20_34"},
                 {"test/rcpsp-max/psp_d_335"},
                 {"test/rcpsp-max/psp_c_362"},
                 {"test/rcpsp-max/psp_c_51"},
                 {"test/rcpsp-max/psp_j30_168"},
                 {"test/rcpsp-max/psp_j20_35"},
                 {"test/rcpsp-max/psp_c_314"},
                 {"test/rcpsp-max/psp_j30_123"},
                 {"test/rcpsp-max/psp_j30_33"},
                 {"test/rcpsp-max/psp_d_13"},
                 {"test/rcpsp-max/psp_ubo200_57"},
                 {"test/rcpsp-max/psp_ubo200_80"},

                //latin-squares-fd

                 {"test/latin-squares-fd/03"},
                 {"test/latin-squares-fd/07"},
                 {"test/latin-squares-fd/10"},
                 {"test/latin-squares-fd/12"},
                 {"test/latin-squares-fd/15"},
                 {"test/latin-squares-fd/20"},
                 {"test/latin-squares-fd/25"},

                //latin-squares-fd2
                {"test/latin-squares-fd2/03"},
                {"test/latin-squares-fd2/07"},
                {"test/latin-squares-fd2/10"},
                {"test/latin-squares-fd2/12"},
                {"test/latin-squares-fd2/15"},
                {"test/latin-squares-fd2/20"},
                {"test/latin-squares-fd2/25"},

                //latin-squares-lp
                {"test/latin-squares-lp/03"},
                {"test/latin-squares-lp/07"},
                {"test/latin-squares-lp/10"},
                {"test/latin-squares-lp/12"},
                {"test/latin-squares-lp/15"},
                {"test/latin-squares-lp/20"},
                {"test/latin-squares-lp/25"},

                //league
                {"test/league/model10-3-4"},
                {"test/league/model15-4-3"},
                {"test/league/model20-3-5"},
                {"test/league/model25-6-5"},
                {"test/league/model30-4-6"},
                {"test/league/model35-6-10"},
                {"test/league/model40-5-12"},
                {"test/league/model45-7-8"},
                {"test/league/model50-4-4"},
                {"test/league/model55-3-12"},
                {"test/league/model60-5-11"},
                {"test/league/model65-13-16"},
                {"test/league/model70-16-3"},
                {"test/league/model75-7-7"},
                {"test/league/model80-18-8"},
                {"test/league/model85-7-16"},
                {"test/league/model90-18-20"},
                {"test/league/model95-12-18"},
                {"test/league/model100-21-12"},

                //linear-to-program
                {"test/linear-to-program/l2p1"},
                {"test/linear-to-program/l2p2"},
                {"test/linear-to-program/l2p12"},
                {"test/linear-to-program/l2p13"},
                {"test/linear-to-program/l2p16"},

                //liner-sf-repositioning
                {"test/liner-sf-repositioning/fm3_5"},
                {"test/liner-sf-repositioning/fm3_11"},
                {"test/liner-sf-repositioning/tp7_0"},
                {"test/liner-sf-repositioning/tp7_8"},
                {"test/liner-sf-repositioning/tp7_10"},

                //magicseq

                {"test/magicseq/005"},
                {"test/magicseq/010"},
                {"test/magicseq/020"},
                {"test/magicseq/030"},
                {"test/magicseq/040"},
                {"test/magicseq/050"},
                {"test/magicseq/100"},
                {"test/magicseq/300"},
                {"test/magicseq/500"},


                //mario
                {"test/mario/mario_easy_2"},
                {"test/mario/mario_easy_4"},
                {"test/mario/mario_easy_5"},
                {"test/mario/mario_n_medium_2"},
                {"test/mario/mario_n_medium_3"},
                {"test/mario/mario_n_medium_4"},
                {"test/mario/mario_n_medium_5"},
                {"test/mario/mario_t_hard_1"},
                {"test/mario/mario_t_hard_2"},
                {"test/mario/mario_t_hard_5"},

                //market_split
                {"test/market_split/s5-09"},
                {"test/market_split/s5-10"},
                {"test/market_split/u3-01"},
                {"test/market_split/u3-02"},
                {"test/market_split/u3-03"},
                {"test/market_split/u3-04"},
                {"test/market_split/u3-05"},
                {"test/market_split/u3-06"},
                {"test/market_split/u3-07"},
                {"test/market_split/u3-08"},
                {"test/market_split/u3-09"},
                {"test/market_split/u3-10"},
                {"test/market_split/u4-01"},
                {"test/market_split/u4-02"},
                {"test/market_split/u4-03"},
                {"test/market_split/u4-05"},
                {"test/market_split/u4-06"},
                {"test/market_split/u4-07"},
                {"test/market_split/u4-08"},
                {"test/market_split/u4-09"},
                {"test/market_split/u4-10"},
                {"test/market_split/u5-01"},
                {"test/market_split/u5-02"},
                {"test/market_split/u5-03"},
                {"test/market_split/u5-04"},
                {"test/market_split/u5-05"},
                {"test/market_split/u5-06"},
                {"test/market_split/u5-07"},
                {"test/market_split/u5-08"},
                {"test/market_split/u5-09"},
                {"test/market_split/u5-10"},

                //mqueens2
                {"test/mqueens2/n11"},
                {"test/mqueens2/n12"},
                {"test/mqueens2/n13"},
                {"test/mqueens2/n20"},
                {"test/mqueens2/n31"},

                //mspsp
                {"test/mspsp/hard_02"},
                {"test/mspsp/hard_03"},
                {"test/mspsp/hard_04"},
                {"test/mspsp/hard_05"},
                {"test/mspsp/hard_06"},
                {"test/mspsp/hard_07"},
                {"test/mspsp/hard_08"},
                {"test/mspsp/medium_01"},
                {"test/mspsp/medium_02"},
                {"test/mspsp/medium_03"},
                {"test/mspsp/medium_04"},
                {"test/mspsp/medium_05"},
                {"test/mspsp/medium_06"},
                {"test/mspsp/medium_07"},

                //stochastic-vrp
                {"test/stochastic-vrp/vrp-s2-v2-c7_vrp-v2-c7_det"},
                {"test/stochastic-vrp/vrp-s3-v2-c6_vrp-v2-c6_det"},
                {"test/stochastic-vrp/vrp-s3-v2-c7_vrp-v2-c7_det"},
                {"test/stochastic-vrp/vrp-s4-v2-c6_vrp-v2-c6_det"},

                //stochastic-fjsp
                {"test/stochastic-fjsp/fjsp-a1-s2_fjsp-t15-j3-m3-a1_det"},
                {"test/stochastic-fjsp/fjsp-a1-s3_fjsp-t20-j4-m3-a1_det"},
                {"test/stochastic-fjsp/fjsp-a1-s4_fjsp-t8-j2-m3-a1_det"},
                {"test/stochastic-fjsp/fjsp-a1-s5_fjsp-t8-j2-m3-a1_det"},
                {"test/stochastic-fjsp/fjsp-a1-s6_fjsp-t8-j2-m3-a1_det"},

                //table-layout
                 {"test/table-layout/1000-1439-line292"},
                 {"test/table-layout/en-760-310-line795"},
                 {"test/table-layout/en-1000-251-line273"},
                 {"test/table-layout/en-1000-274-line403"},
                 {"test/table-layout/en-1000-1274-line521"},
                 {"test/table-layout/en-1000-1286-line764"},
                 {"test/table-layout/en-1000-1303-line283"},
                 {"test/table-layout/en-1000-1303-line1078"},
                 {"test/table-layout/en-1000-1407-line976"},
                 {"test/table-layout/en-1000-1407-line1350"},
                 {"test/table-layout/en-1000-1407-line1986"},
                 {"test/table-layout/en-1000-1479-line419"},
                 {"test/table-layout/en-1000-1479-line1099"},
                 {"test/table-layout/en-1000-1615-line479"},
                 {"test/table-layout/en-1250-158-line1950"},
                 {"test/table-layout/en-1250-1074-line298"},
                 {"test/table-layout/en-1250-1261-line126"},
                 {"test/table-layout/en-1250-1283-line119"},
                 {"test/table-layout/en-1250-1303-line283"},
                 {"test/table-layout/en-1250-1305-line158"},
                 {"test/table-layout/en-1250-1407-line976"},
                 {"test/table-layout/en-1250-1407-line1350"},
                 {"test/table-layout/en-1250-1407-line1986"},
                 {"test/table-layout/en-1250-1479-line419.dzn"},
                 {"test/table-layout/en-1250-1479-line1099"},
                 {"test/table-layout/en-1250-1479-line1633"},

                //parity-learning
                 {"test/parity-learning/44_22_5.1"},
                 {"test/parity-learning/44_22_5.2"},
                 {"test/parity-learning/44_22_5.3"},
                 {"test/parity-learning/48_24_6.1"},
                 {"test/parity-learning/48_24_6.2"},
                 {"test/parity-learning/48_24_6.3"},
                 {"test/parity-learning/52_26_6.1"},
                 {"test/parity-learning/52_26_6.2"},
                 {"test/parity-learning/52_26_6.3"},

                //pattern_set_mining_k1
                {"test/pattern_set_mining_k1/anneal"},
                {"test/pattern_set_mining_k1/audiology"},
                {"test/pattern_set_mining_k1/german-credit"},
                {"test/pattern_set_mining_k1/hepatitis"},
                {"test/pattern_set_mining_k1/hypothyroid"},
                {"test/pattern_set_mining_k1/ionosphere"},
                {"test/pattern_set_mining_k1/kr-vs-kp"},
                {"test/pattern_set_mining_k1/mushroom"},
                {"test/pattern_set_mining_k1/pattern_set_mining_k1.mzn
                {"test/pattern_set_mining_k1/segment"},
                {"test/pattern_set_mining_k1/sonar"},
                {"test/pattern_set_mining_k1/splice-1"},
                {"test/pattern_set_mining_k1/vehicle"},
                {"test/pattern_set_mining_k1/vowel"},
                {"test/pattern_set_mining_k1/waveform-5000"},
                {"test/pattern_set_mining_k1/yeast"},




                //CELAR6-SUB0
                 {"test/celar/CELAR6-SUB0"},
                 {"test/celar/CELAR6-SUB4"},
                 {"test/celar/CELAR7-SUB4"},
                 {"test/celar/graph05"},
                 {"test/celar/scen07"},

                 //cryptanalysis
                 {"test/cryptanalysis/kb128_n5_obj11"},
                 {"test/cryptanalysis/kb128_n5_obj14"},
                 {"test/cryptanalysis/kb128_n5_obj16"},
                 {"test/cryptanalysis/kb128_n5_obj17"},
                 {"test/cryptanalysis/kb192_n7_obj10"},

                //depot-placement
                  {"test/depot-placement/att48_6"},
                  {"test/depot-placement/rat99_5"},
                  {"test/depot-placement/rat99_6"},
                  {"test/depot-placement/st70_5"},
                  {"test/depot-placement/ulysses22_5"},

                //diameterc-mst
                  {"test/diameterc-mst/c_v20_a190_d5"},
                  {"test/diameterc-mst/c_v15_a105_d7"},
                  {"test/diameterc-mst/s_v20_a50_d4"},
                  {"test/diameterc-mst/s_v20_a50_d5"},
                  {"test/diameterc-mst/s_v40_a100_d5"},

                //elitserien
                  {"test/elitserien/handball3"},
                  {"test/elitserien/handball5"},
                  {"test/elitserien/handball7"},
                  {"test/elitserien/handball17"},
                  {"test/elitserien/handball20"},




                //gbac
                 //java.lang.AssertionError: Two variables have the same id counter0::{0..6} counter0::{0..6}
                // {"test/gbac/reduced_UD3-gbac"},
                //java.lang.AssertionError: Two variables have the same id counter0::{0..4} counter0::{0..8}
                //  {"test/gbac/reduced_UD6-gbac"},
                 //java.lang.AssertionError: Two variables have the same id counter0::{0..5} counter0::{0..6}
                // {"test/gbac/reduced_UD10-gbac"},
                //%% Evaluation of model resulted in an overflow.
               // java.lang.IndexOutOfBoundsException: Index: 0, Size: 0
               // {"test/gbac/UD3-gbac"},
                 //%% Evaluation of model resulted in an overflow.
                //java.lang.IndexOutOfBoundsException: Index: 0, Size: 0
                //  {"test/gbac/UD5-gbac"},


                //gfd-schedule
                {"upTo30sec/gfd-schedule/n120f5d50m50k20"},
                {"upTo5sec/gfd-schedule/n180f7d50m30k18"},
                 {"test/gfd-schedule/n25f5d20m10k3"},
                 {"test/gfd-schedule/n35f5d20m10k3"},
                 {"test/gfd-schedule/n55f2d50m30k3"},
                 {"test/gfd-schedule/n60f7d50m30k10"},
                 {"test/gfd-schedule/n180f7d50m30k18"},

                //mapping
                {"upTo5sec/mapping/full2x2"},
                {"upTo30sec/mapping/mesh3x3_2"},
                {"upTo5min/mapping/mesh2x2_mpeg"},
                {"upTo5sec/mapping/mesh2x2_1"},
                {"upTo5min/mapping/mesh2x2_mp3"},
                {"test/mapping/mesh3x3_mp3"},
                {"test/mapping/mesh4x4_1"},
                {"test/mapping/ring_1"},

                //maximum-dag
                {"test/maximum-dag/25_01"},
                {"test/maximum-dag/25_03"},
                {"test/maximum-dag/25_04"},
                {"test/maximum-dag/25_06"},
                {"test/maximum-dag/31_02"},



                //mrcpsp
                {"test/mrcpsp/j30_1_10"},
                {"test/mrcpsp/j30_15_5"},
                {"test/mrcpsp/j30_17_10"},
                {"test/mrcpsp/j30_37_4"},
                {"test/mrcpsp/mrcpsp"},

                //nfc
                {"upTo5sec/nfc/12_2_5"},
                {"upTo5sec/nfc/12_2_10"},
                {"upTo5sec/nfc/18_3_5"},
                {"upTo5sec/nfc/18_3_10"},

                //java.lang.AssertionError: non-optimal arcs:
                //[n_22->n_23, flow=1/1  reduced=2, index=9, forward = true, companion = [offset = 91, xVar = X_INTRODUCED_22, wVar = _13}]]
                //{"test/nfc/24_4_10"},

                //oocsp_racks
                 {"test/oocsp_racks/oocsp_racks_030_e6_cc"},
                 {"test/oocsp_racks/oocsp_racks_030_ea4_cc"},
                 {"test/oocsp_racks/oocsp_racks_030_f7_cc"},
                 {"test/oocsp_racks/oocsp_racks_030_mii8"},
                 {"test/oocsp_racks/oocsp_racks_100_r1"},
*/
                //prize-collecting
                {"upTo5sec/prize-collecting/28-4-7-1"},
                {"upTo5min/prize-collecting/30-5-6-2"},
                {"upTo5min/prize-collecting/30-5-6-8"},
                {"upTo1hour/prize-collecting/32-4-8-2"},
                {"upTo1hour/prize-collecting/32-4-8-5"},

                //rcpsp-wet
                {"test/rcpsp-wet/j30_27_5-wet"},
                {"test/rcpsp-wet/j30_44_8-wet"},
                {"test/rcpsp-wet/j60_36_8-wet"},
                {"test/rcpsp-wet/j90_10_10-wet"},
                {"test/rcpsp-wet/j90_19_7-wet"},

                //solbat
                 {"test/solbat/sb_13_13_5_1"},
                 {"test/solbat/sb_13_13_5_5"},
                 {"test/solbat/sb_15_15_6_0"},
                 {"test/solbat/sb_15_15_7_3"},
                 {"test/solbat/sb_15_15_7_5"},

                //tpp
                 {"test/tpp/tpp_4_5_20_1"},
                 {"test/tpp/tpp_5_3_30_1"},
                 {"test/tpp/tpp_6_3_20_1"},
                 {"test/tpp/tpp_7_3_20_1"},
                 {"test/tpp/tpp_7_3_30_1"},

                //zephyrus
                 {"test/zephyrus/12__6__8__3"},
                 {"test/zephyrus/12__8__6__3"},
                 {"test/zephyrus/14__6__8__3"},
                 {"test/zephyrus/14__8__6__3"},
                 {"test/zephyrus/14__10__8__3"},

                //stable_roommates
                {"test/stable_roommates/sm6"},
                {"test/stable_roommates/sri6"},

                //stable_roommates_func
                {"test/stable_roommates_func/sm6_func"},
                {"test/stable_roommates_func/sri6_func"},

                //submultisetsum
                {"test/submultisetsum/submultisetsum"},

                //restert
                {"test/restart/restart"},
                {"test/restart/restart2"},

                //restarta
                {"test/restarta/restarta"},

                //slow_convergence
                {"test/slow_convergence/0100"},
                {"test/slow_convergence/0200"},
                {"test/slow_convergence/0300"},
                {"test/slow_convergence/0400"},
                {"test/slow_convergence/0500"},
                {"test/slow_convergence/0600"},
                {"test/slow_convergence/0700"},
                {"test/slow_convergence/0800"},
                {"test/slow_convergence/0900"},
                {"test/slow_convergence/1000"},

                //schur_numbers
                {"test/schur_numbers/5-3"},
                {"test/schur_numbers/7-3"},
                {"test/schur_numbers/10-3"},

                //search_stress
                {"test/search_stress/search_stress"},

                //proteindesign12
                {"test/proteindesign12/1HZ5.12p.9aa.usingEref_self"},
                {"test/proteindesign12/1HZ5.12p.19aa.usingEref_self"},
                {"test/proteindesign12/1PGB.11p.9aa.usingEref_self"},
                {"test/proteindesign12/1UBI.13p.9aa.usingEref_self"},

                //search_stress2
                {"test/search_stress2/search_stress2"},

                //still-life-wastage
                {"test/still-life-wastage/09"},
                {"test/still-life-wastage/10."},
                {"test/still-life-wastage/11"},
                {"test/fz/test/still-life-wastage/13"},

                //wwtpp-random

                /*
               //timeout{"above1hour/amaze/2012-04-27"},
               //java.lang.IndexOutOfBoundsException: Index: 0, Size: 0
               //{"above1hour/amaze/2012-04-30"},
               //java.lang.IndexOutOfBoundsException: Index: 0, Size: 0
               //{"above1hour/amaze/2012-05-02"},
               //java.lang.IndexOutOfBoundsException: Index: 0, Size: 0
               //{"above1hour/amaze/2012-05-03"},
               //java.lang.IndexOutOfBoundsException: Index: 0, Size: 0
               //java.lang.IndexOutOfBoundsException: Index: 0, Size: 0
               //{"above1hour/amaze/2012-05-15"},
               //java.lang.IndexOutOfBoundsException: Index: 0, Size: 0
               //{"above1hour/amaze/2012-05-31"},
               //java.lang.IndexOutOfBoundsException: Index: 0, Size: 0
               //{"above1hour/amaze/2012-06-01"},
               //java.lang.IndexOutOfBoundsException: Index: 0, Size: 0
               //{"above1hour/amaze/2012-06-07"},
               //java.lang.IndexOutOfBoundsException: Index: 0, Size: 0
               //{"above1hour/amaze/2012-06-26"},
               //java.lang.IndexOutOfBoundsException: Index: 0, Size: 0
               //{"above1hour/amaze/2012-06-27"},
               //java.lang.IndexOutOfBoundsException: Index: 0, Size: 0
               //{"above1hour/amaze/2012-06-28"},
               //timeout{"above1hour/amaze/2012-06-29"},

               //largescheduling
               //%% Stack overflow exception error;
               {"largescheduling/instance-0100-1"},

               // %% Stack overflow exception error; consider option -Xss... for JVM
               {"largescheduling/instance-0400-2"},

               //%% Stack overflow exception error; consider option -Xss... for JVM
               {"largescheduling/instance-0800-1"},

               //%% Stack overflow exception error; consider option -Xss... for JVM
               {"largescheduling/instance-1600-2"},

               //java.lang.AssertionError: non-optimal arcs:
               {"mapping/mesh3x3_mpeg_2"},

               //java.lang.AssertionError: non-optimal arcs:
               {"mapping/ring_2.dzn"},


               //java.lang.IndexOutOfBoundsException
               {"radiation/i14-9"},

               //triangular
               //%% Parser exception
               {"/triangular/n10"},

               //%% Parser exception
               {"triangular/n16"},

               //%% Parser exception
               {"triangular/n22"},

               //%% Parser exception
               {"triangular/n28"},

               //%%Parser exception
               {"triangular/n37"},

               //225_divisor
               //java.lang.NumberFormatException: For input string: "-10000000000"
               //java.lang.NumberFormatException: For input string: "-10000000000"
               {"225_divisor/225_divisor"}

               ////arrow
               //%%java.lang.ArithmeticException: Too large bounds on intervals 123456789..987654321
               {"arrow/arrow"},

               //artificial_intelligence
               //java.lang.NumberFormatException: For input string: "11000098990"
               {"/artificial_intelligence/artificial_intelligence"},

               //birthdays_coins
               //%%java.lang.ArithmeticException: Overflow occurred from int -2100000000 + -300000000
               {"/birthdays_coins/birthdays_coins"},

               //birthdays_coins
               //%%java.lang.ArithmeticException: Overflow occurred from int -2100000000 + -300000000
               {"/birthdays_coins/birthdays_coins"},

               //blending
               //java.lang.AssertionError: Request for a value of not grounded variable z::{733.0373723874923..733.0375161858722}
               {"/blending/blending"},

               //candies
               //%%java.lang.ArithmeticException: Too large bounds on intervals 1233..123300000
               {"/candies/candies"},

               //225_divisor
               //java.lang.NumberFormatException: For input string: "-10000000000"
               {"/225_divisor/225_divisor"},

               //arrow
               //%%java.lang.ArithmeticException: Too large bounds on intervals 123456789..987654321
               {"/arrow/arrow"},

               //artificial_intelligence
               //java.lang.NumberFormatException: For input string: "11000098990"
               {"/artificial_intelligence/artificial_intelligence"},

               //euler_2
               //%%java.lang.ArithmeticException: Overflow occurred from int -2100000000 + -50000000
               {"/euler_2/euler_2"},

               //digits_of_the_square
               //%%java.lang.ArithmeticException: Too large bounds on intervals 1000000..99980001
               {"/digits_of_the_square/digits_of_the_square"},

               //birthdays_coins
               //%% Evaluation of model resulted in an overflow.
               //%%java.lang.ArithmeticException: Overflow occurred from int -2100000000 + -300000000
               {"birthdays_coins/birthdays_coins"},

               //blending
               //java.lang.AssertionError: Request for a value of not grounded variable z::{733.0373723874923..733.0375161858722}
               {"blending/blending"},

               //seating_arrangements_1
               //java.lang.AssertionError
               {"seating_arrangements/seating_arrangements_1"},

               //java.lang.AssertionError
               {"seating_arrangements/seating_arrangements_2"},

               //candies
               //%%java.lang.ArithmeticException: Too large bounds on intervals 1233..123300000
               {"candies/candies"},

               //coins
               //%%java.lang.ArithmeticException: Overflow occurred from int -1550000000 + -850000000
               {"coins/coins"},

               //contains_array
               //%%java.lang.ArithmeticException: Too large bounds on intervals 123402345..123402345
               {"/contains_array/contains_array"},

               //cookie_bake_off2
               //java.lang.AssertionError: Request for a value of not grounded variable diffs_sum::{148.8608479334477..148.88394192594498}
               {"/cookie_bake_off2/cookie_bake_off2"},

               //crypt_reversed
               //%%java.lang.ArithmeticException: Too large bounds on intervals 100000000..999999999
               {"/crypt_reversed/crypt_reversed"},

               //cur_num
               //%%java.lang.ArithmeticException: Overflow occurred from int 4000000 * 4000000
               {"/cur_num/cur_num"},

               //curious_set_of_integers
               //%%java.lang.ArithmeticException: Too large bounds on intervals 0..100000000
               {"/curious_set_of_integers/curious_set_of_integers"},

               //curve_fitting1
               //java.lang.AssertionError: Request for a value of not grounded variable z::{13.794108116596847..13.794376106502922}
               {"/curve_fitting1/curve_fitting1"},

               //dea
               //java.lang.AssertionError: Request for a value of not grounded variable X_INTRODUCED_4831::{3.4169921874999964..3.4212036132812536}
               {"/dea/dea"},

               //debruijn2d_2
               //%%java.lang.ArithmeticException: Too large bounds on intervals 0..387420488
               {"/debruijn2d_2/debruijn2d_2"}

               //diet1
               //%%java.lang.ArithmeticException: Overflow occurred from int -33333331 * -400
               {"/diet1/diet1"},

               //divisible_by_1_to_9
               //%%java.lang.ArithmeticException: Too large bounds on intervals 0..99999999
               {"/divisible_by_1_to_9/divisible_by_1_to_9"},

               //divisible_by_9_through_1
               //%%java.lang.ArithmeticException: Too large bounds on intervals 111111111..999999999
               {"/divisible_by_9_through_1/divisible_by_9_through_1"},

               //dynamical_optimization1
               //java.lang.AssertionError: Request for a value of not grounded variable cost::{36.886716755850856..36.89073504844621}
               {"/dynamical_optimization1/dynamical_optimization1"},

               //enigma_1557
               //%% Stack overflow exception error; consider option -Xss... for JVM
               //{"/enigma_1557/enigma_1557"},

               //enigma_1570
               //%%java.lang.ArithmeticException: Too large bounds on intervals 0..129847036
               //%% Evaluation of model resulted in an overflow.
               {"/enigma_1570/enigma_1570"}

               //enigma_1574
               //%%	java.lang.ArithmeticException: Overflow occurred from int 50000000 * 50000000
               {"/enigma_1574/enigma_1574"},

               //enigma_1575
               //java.lang.AssertionError: Operation mod does not hold w = 1 mod _1 = 3 = _9 = 0(result 0..1
               {"/enigma_1575/enigma_1575"},

               //enigma_portuguese_squares
               //%%java.lang.ArithmeticException: Too large bounds on intervals 1..1000000000
               {"/enigma_portuguese_squares/enigma_portuguese_squares"},

               //euler_52
               //%%java.lang.ArithmeticException: Too large bounds on intervals 1..999999999
               {"/euler_52/euler_52"},

               //food
               //%% Stack overflow exception error; consider option -Xss... for JVM
               {"/food/food"},

               //ice_cream
               //%%	java.lang.ArithmeticException: Overflow occurred from int 50000000 * 50
               {"/ice_cream/ice_cream"},

               //four_power
               //%%	java.lang.ArithmeticException: Too large bounds on intervals 1..64000000
               {"/four_power/four_power"},

               //furniture
               //%%	java.lang.ArithmeticException: Too large bounds on intervals 0..130186980
               {"furniture/furniture"},

               //grocery
               //%%java.lang.ArithmeticException: Too large bounds on intervals 0..359425431
               //%% Evaluation of model resulted in an overflow.
               {"/grocery/grocery"},

               //hardy_1729
               //%%	java.lang.ArithmeticException: Overflow occurred from int 50000000 * 50000000
               //%% Evaluation of model resulted in an overflow.
               {"/hardy_1729/hardy_1729"},

               //home_improvement
               //%% Stack overflow exception error; consider option -Xss... for JVM
               {"/home_improvement/home_improvement"},

               //knapsack_rosetta_code_unbounded_int
               //%%	java.lang.ArithmeticException: Overflow occurred from int 50000000 * 3000
               {"knapsack_rosetta_code_unbounded_int/knapsack_rosetta_code_unbounded_int"},

               //missing_digit
               //%%java.lang.ArithmeticException: Too high or low value for domain assignment int_lin_eq([-100000000, -10000000, -1000000, -100000, -10000, -1000, -100, -10, -1], [X_INTRODUCED_0::{0..9}, X_INTRODUCED_1::{0..9}, X_INTRODUCED_2::{0..9}, X_INTRODUCED_3::{0..9}, X_INTRODUCED_4::{0..9}, X_INTRODUCED_5::{0..9}, X_INTRODUCED_6::{0..9}, X_INTRODUCED_7::{0..9}, X_INTRODUCED_8::{0..9}], -536870912)
               //{"missing_digit/missing_digit"},

               //money_change
               //%%java.lang.ArithmeticException: Overflow occurred from int -50000000 * 50
               {"money_change/money_change"},

               //number_puzzle
               //%% Stack overflow exception error; consider option -Xss... for JVM
               {"number_puzzle/number_puzzle"},

               //number_square
               //%%java.lang.ArithmeticException: Too large bounds on intervals 110000000..199999999
               {"number_square/number_square"},

               //java.lang.IndexOutOfBoundsException: Index: 0, Size: 0
               {"numberlink/numberlink6"},

               //%% Stack overflow exception error; consider option -Xss... for JVM
               {"scheduling_with_assignments/scheduling_with_assignments16c"},

               //%% Stack overflow exception error; consider option -Xss... for JVM
               {"scheduling_with_assignments/scheduling_with_assignments16e" },

               //%% Stack overflow exception error; consider option -Xss... for JVM
               {"scheduling_with_assignments/scheduling_with_assignments16f"},

               //coins
               //%%java.lang.ArithmeticException: Overflow occurred from int -1550000000 + -850000000 //
               {"coins/coins"},

               //nonlin2
               //%%java.lang.ArithmeticException: Overflow occurred from int 50000000 * 50000000
               {"nonlin2/nonlin2"},

               //pandigital_numbers
               //%	java.lang.ArithmeticException: Overflow occurred from int 99996 * 99997
               {"pandigital_numbers/pandigital_numbers"},

               //plan
               //java.lang.AssertionError: Request for a value of not grounded variable value::{361.7445664788383..361.7446692706953}
               {"plan//plan"},

               //product_configuration
               //%%	java.lang.ArithmeticException: Overflow occurred from int -50000000 * 50
               {"product_configuration/product_configuration"},

               //public_school_problem
               //%%	java.lang.ArithmeticException: Overflow occurred from int -1900000000 + -650000000
               {"public_school_problem/public_school_problem"},

               //pythagoras.fzn
               //%%	java.lang.ArithmeticException: Overflow occurred from int 49999999 * 49999999
               {"pythagoras/pythagoras"},

               //rosenbrock
               //java.lang.AssertionError: Request for a value of not grounded variable z::{403.9173340146463..404.0000000000004}
               {"rosenbrock/rosenbrock"},

               //seating_arrangements
               //java.lang.AssertionError
               {"seating_arrangements/seating_arrangements_1"},

               //java.lang.AssertionError
               {"seating_arrangements/seating_arrangements_21"},

               //seven11
               //%%java.lang.ArithmeticException: Too large bounds on intervals 0..359425431
               //%% Evaluation of model resulted in an overflow.
               {"seven11/seven11"},

               //transportation
               //%% Evaluation of model resulted in an overflow.
               //transportation/transportation"},
               //%%java.lang.ArithmeticException: Overflow occurred from int -2050000000 + -250000000
               {"transportation/transportation"},

               //transportation2
               //%%java.lang.ArithmeticException: Overflow occurred from int 1950000000 + 250000000
               //%% Evaluation of model resulted in an overflow.
               {"transportation2/transportation2"},

               //volsay2
               //java.lang.AssertionError: Request for a value of not grounded variable -z::{-7.152557373046877E-4..-0.0}
               {"volsay2/volsay2"},

               //smallest_winning_electoral2
               // %%java.lang.ArithmeticException: Too large bounds on intervals 0..311591917
               //%% Evaluation of model resulted in an overflow.
               {"smallest_winning_electoral2/smallest_winning_electoral2"},

               //square_root_of_wonderful
               //%% Evaluation of model resulted in an overflow.
               //%%java.lang.ArithmeticException: Too large bounds on intervals 111111111..999999999
               {"square_root_of_wonderful/square_root_of_wonderful"},

               //subset_sum
               //%%java.lang.ArithmeticException: Overflow occurred from int -1650000000 + -1150000000
               //%% Evaluation of model resulted in an overflow.
               {"subset_sum/subset_sum"},

               //tea_mixing
               //%% Evaluation of model resulted in an overflow.
               {"tea_mixing/tea_mixing"},}",

               //%%java.lang.ArithmeticException: Overflow occurred from int -1500000000 + -1350000000
               {"tea_mixing/tea_mixing"},

               //to_num
               //java.lang.NumberFormatException: For input string: "9999999999"
               {"to_num/to_num"},

               //tobacco
               //%% Evaluation of model resulted in an overflow.
               //tobacco/tobacco"}
               //%%java.lang.ArithmeticException: Overflow occurred from int -50000000 * 49
               {"tobacco/tobacco"},

               //kordemskys_palindrome_problem
               //java.lang.NumberFormatException: For input string: "9999999999"
               {"kordemskys_palindrome_problem/kordemskys_palindrome_problem"},

               //cluster
                //Symbol "X_INTRODUCED_65" does not have assigned value when refered; execution aborted
                // {"cluster/cluster"},

                //2DBinPacking
                {"errors/2DBinPacking/Class1_20_1"},
                {"errors/2DBinPacking/Class1_20_2"},
                {"errors/2DBinPacking/Class1_20_3"},
                {"errors/2DBinPacking/Class1_20_4"},
                {"errors/2DBinPacking/Class1_20_5"},
                {"errors/2DBinPacking/Class1_20_6"},
                {"errors/2DBinPacking/Class1_20_7"},
                {"errors/2DBinPacking/Class1_20_8"},
                {"errors/2DBinPacking/Class1_20_9"},
                {"errors/2DBinPacking/Class1_20_10"},
                {"errors/2DBinPacking/Class1_40_1"},
                {"errors/2DBinPacking/Class1_40_2"},
                {"errors/2DBinPacking/Class1_40_3"},
                {"errors/2DBinPacking/Class1_40_4"},
                {"errors/2DBinPacking/Class1_40_5"},
                {"errors/2DBinPacking/Class1_40_6"},
                {"errors/2DBinPacking/Class1_40_7"},
                {"errors/2DBinPacking/Class1_40_8"},
                {"errors/2DBinPacking/Class1_40_9"},
                {"errors/2DBinPacking/Class1_40_10"},
                {"errors/2DBinPacking/Class1_60_1"},
                {"errors/2DBinPacking/Class1_60_2"},
                {"errors/2DBinPacking/Class1_60_3"},
                {"errors/2DBinPacking/Class1_60_4"},
                {"errors/2DBinPacking/Class1_60_5"},
                {"errors/2DBinPacking/Class1_60_6"},
                {"errors/2DBinPacking/Class1_60_7"},
                {"errors/2DBinPacking/Class1_60_8"},
                {"errors/2DBinPacking/Class1_60_9"},
                {"errors/2DBinPacking/Class1_60_10"},
                {"errors/2DBinPacking/Class1_80_1"},
                {"errors/2DBinPacking/Class1_80_2"},
                {"errors/2DBinPacking/Class1_80_3"},
                {"errors/2DBinPacking/Class1_80_4"},
                {"errors/2DBinPacking/Class1_80_5"},
                {"errors/2DBinPacking/Class1_80_6"},
                {"errors/2DBinPacking/Class1_80_7"},
                {"errors/2DBinPacking/Class1_80_8"},
                {"errors/2DBinPacking/Class1_80_9"},
                {"errors/2DBinPacking/Class1_80_10"},
                {"errors/2DBinPacking/Class1_100_1"},
                {"errors/2DBinPacking/Class1_100_2"},
                {"errors/2DBinPacking/Class1_100_3"},
                {"errors/2DBinPacking/Class1_100_4"},
                {"errors/2DBinPacking/Class1_100_5"},
                {"errors/2DBinPacking/Class1_100_6"},
                {"errors/2DBinPacking/Class1_100_7"},
                {"errors/2DBinPacking/Class1_100_8"},
                {"errors/2DBinPacking/Class1_100_9"},
                {"errors/2DBinPacking/Class1_100_10"},

       */

        });
    }



    @Test(timeout=5400000)
    public void testMinizinc() throws IOException {

        List<String> expectedResult = expected(this.inputString + ".out");
        List<String> result = result(this.inputString + ".fzn");

        for(int i=0; i<result.size(); i++) {
            assertEquals("\n" + "File path: " + inputString + ".out " +"\nError line number: " + (i+1) + "\n",
                         expectedResult.get(i), result.get(i));
        }

    }


    public static List<String> result(String filename) {
        ByteArrayOutputStream baos = new ByteArrayOutputStream();
        PrintStream old = System.out;
        System.setOut(new PrintStream(baos));


        fz2jacop.main(new String[]{relativePath + filename });

        System.out.flush();
        System.setOut(old);

        String result = baos.toString();
        if(printInfo) {
            System.out.println(filename+"\n" + result);
        }

        return Arrays.asList(result.split("\n"));
    }


    public static List<String> expected(String filename) throws IOException {

        String filePath = new File(relativePath + filename ).getAbsolutePath();


        return Files.readAllLines(Paths.get(filePath), StandardCharsets.UTF_8);
    }


}
