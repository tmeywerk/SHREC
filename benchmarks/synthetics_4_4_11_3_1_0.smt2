(set-logic QF_LRA)
(declare-fun b2 () Bool)
(declare-fun b0 () Bool)
(declare-fun r0 () Real)
(declare-fun r1 () Real)
(declare-fun r2 () Real)
(declare-fun b1 () Bool)
(declare-fun r3 () Real)
(declare-fun b3 () Bool)
(assert (let ((.def_0 (* (/ 549030803386503 562949953421312) r3))) (let ((.def_1 (* (/ 2546356573677109 4503599627370496) r2))) (let ((.def_2 (* (- (/ 1688877791699459 2251799813685248)) r1))) (let ((.def_3 (* (/ 3326781100761405 9007199254740992) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (/ 4002766934190047 4503599627370496)))) (let ((.def_6 (or b0 b1 .def_5))) (let ((.def_7 (* (/ 813100539869503 9007199254740992) r3))) (let ((.def_8 (* (- (/ 869353132897559 562949953421312)) r2))) (let ((.def_9 (* (- (/ 1610579251618473 2251799813685248)) r1))) (let ((.def_10 (* (/ 7314970528646215 9007199254740992) r0))) (let ((.def_11 (+ .def_10 .def_9 .def_8 .def_7))) (let ((.def_12 (<= .def_11 (- (/ 3138944043053369 9007199254740992))))) (let ((.def_13 (not b3))) (let ((.def_14 (or .def_13 b2 .def_12))) (let ((.def_15 (* (- (/ 3393612091820525 2251799813685248)) r3))) (let ((.def_16 (* (/ 4561939839556883 4503599627370496) r2))) (let ((.def_17 (* (/ 984262341384611 1125899906842624) r1))) (let ((.def_18 (* (- (/ 4575207827514517 9007199254740992)) r0))) (let ((.def_19 (+ .def_18 .def_17 .def_16 .def_15))) (let ((.def_20 (<= .def_19 (/ 1274120615580977 9007199254740992)))) (let ((.def_21 (not b1))) (let ((.def_22 (not b2))) (let ((.def_23 (or .def_22 .def_21 .def_20))) (let ((.def_24 (* (- (/ 911800408947731 562949953421312)) r3))) (let ((.def_25 (* (- (/ 362223178561705 281474976710656)) r2))) (let ((.def_26 (* (- (/ 1900858159703273 1125899906842624)) r1))) (let ((.def_27 (* (/ 6142645735757105 4503599627370496) r0))) (let ((.def_28 (+ .def_27 .def_26 .def_25 .def_24))) (let ((.def_29 (<= .def_28 (- (/ 540119295785385 562949953421312))))) (let ((.def_30 (or b2 b1 .def_29))) (let ((.def_31 (* (- (/ 2983701865823195 2251799813685248)) r3))) (let ((.def_32 (* (/ 2688282206266479 2251799813685248) r2))) (let ((.def_33 (* (- (/ 3957593545183559 4503599627370496)) r1))) (let ((.def_34 (* (/ 67316004173301 562949953421312) r0))) (let ((.def_35 (+ .def_34 .def_33 .def_32 .def_31))) (let ((.def_36 (<= .def_35 (- (/ 494067065878627 4503599627370496))))) (let ((.def_37 (or .def_13 b0 .def_36))) (let ((.def_38 (* (- (/ 381649514161391 9007199254740992)) r3))) (let ((.def_39 (* (/ 745313491314957 562949953421312) r2))) (let ((.def_40 (* (- (/ 27533133471441 140737488355328)) r1))) (let ((.def_41 (* (- (/ 1147294343304969 1125899906842624)) r0))) (let ((.def_42 (+ .def_41 .def_40 .def_39 .def_38))) (let ((.def_43 (<= .def_42 (/ 2756131867716095 9007199254740992)))) (let ((.def_44 (or b2 b0 .def_43))) (let ((.def_45 (* (/ 1068138728877879 2251799813685248) r3))) (let ((.def_46 (* (- (/ 728959527796321 9007199254740992)) r2))) (let ((.def_47 (* (/ 6931142912207407 9007199254740992) r1))) (let ((.def_48 (* (- (/ 3380011411838227 2251799813685248)) r0))) (let ((.def_49 (+ .def_48 .def_47 .def_46 .def_45))) (let ((.def_50 (<= .def_49 (/ 95452437618579 281474976710656)))) (let ((.def_51 (or b1 b2 .def_50))) (let ((.def_52 (* (- (/ 2960395802226921 2251799813685248)) r3))) (let ((.def_53 (* (/ 6711103264772977 9007199254740992) r2))) (let ((.def_54 (* (/ 3585889034071273 4503599627370496) r1))) (let ((.def_55 (* (/ 1447313591944375 9007199254740992) r0))) (let ((.def_56 (+ .def_55 .def_54 .def_53 .def_52))) (let ((.def_57 (<= .def_56 (/ 5833164760990457 9007199254740992)))) (let ((.def_58 (or .def_13 .def_21 .def_57))) (let ((.def_59 (* (/ 677827426495835 281474976710656) r3))) (let ((.def_60 (* (- (/ 2458408278363565 1125899906842624)) r2))) (let ((.def_61 (* (- (/ 1610704287610555 2251799813685248)) r1))) (let ((.def_62 (* (- (/ 5021481660091861 4503599627370496)) r0))) (let ((.def_63 (+ .def_62 .def_61 .def_60 .def_59))) (let ((.def_64 (<= .def_63 (/ 835277401514153 9007199254740992)))) (let ((.def_65 (not b0))) (let ((.def_66 (or .def_65 .def_22 .def_64))) (let ((.def_67 (* (- (/ 949105900655499 9007199254740992)) r3))) (let ((.def_68 (* (/ 1833088043142821 1125899906842624) r2))) (let ((.def_69 (* (- (/ 214490024423793 4503599627370496)) r1))) (let ((.def_70 (* (/ 1995403866605167 9007199254740992) r0))) (let ((.def_71 (+ .def_70 .def_69 .def_68 .def_67))) (let ((.def_72 (<= .def_71 (/ 6290363659733627 4503599627370496)))) (let ((.def_73 (or b0 b3 .def_72))) (let ((.def_74 (* (- (/ 1939625850544765 1125899906842624)) r3))) (let ((.def_75 (* (- (/ 4923743560487341 2251799813685248)) r2))) (let ((.def_76 (* (- (/ 3537180473644199 9007199254740992)) r1))) (let ((.def_77 (* (/ 3606748249868779 4503599627370496) r0))) (let ((.def_78 (+ .def_77 .def_76 .def_75 .def_74))) (let ((.def_79 (<= .def_78 (- (/ 3952009744055113 4503599627370496))))) (let ((.def_80 (or .def_22 .def_65 .def_79))) (let ((.def_81 (and .def_80 .def_73 .def_66 .def_58 .def_51 .def_44 .def_37 .def_30 .def_23 .def_14 .def_6))) .def_81)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)