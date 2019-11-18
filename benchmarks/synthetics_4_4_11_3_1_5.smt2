(set-logic QF_LRA)
(declare-fun b2 () Bool)
(declare-fun b0 () Bool)
(declare-fun r0 () Real)
(declare-fun r1 () Real)
(declare-fun r2 () Real)
(declare-fun b1 () Bool)
(declare-fun r3 () Real)
(declare-fun b3 () Bool)
(assert (let ((.def_0 (* (- (/ 3624862919635955 2251799813685248)) r3))) (let ((.def_1 (* (/ 3982435444300595 9007199254740992) r2))) (let ((.def_2 (* (- (/ 3783299400850101 4503599627370496)) r1))) (let ((.def_3 (* (/ 343149315090601 562949953421312) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (- (/ 2636729712089007 4503599627370496))))) (let ((.def_6 (not b2))) (let ((.def_7 (or b1 .def_6 .def_5))) (let ((.def_8 (* (- (/ 578450392208229 562949953421312)) r3))) (let ((.def_9 (* (/ 3568759459782259 4503599627370496) r2))) (let ((.def_10 (* (/ 247448549326625 4503599627370496) r1))) (let ((.def_11 (* (/ 1948491813252951 4503599627370496) r0))) (let ((.def_12 (+ .def_11 .def_10 .def_9 .def_8))) (let ((.def_13 (<= .def_12 (/ 3764294348910535 9007199254740992)))) (let ((.def_14 (or .def_6 b1 .def_13))) (let ((.def_15 (* (- (/ 503129364472987 1125899906842624)) r3))) (let ((.def_16 (* (/ 2696382654090261 2251799813685248) r2))) (let ((.def_17 (* (/ 1025792445146587 2251799813685248) r1))) (let ((.def_18 (* (- (/ 1860508470995755 1125899906842624)) r0))) (let ((.def_19 (+ .def_18 .def_17 .def_16 .def_15))) (let ((.def_20 (<= .def_19 (- (/ 3584939988229 8796093022208))))) (let ((.def_21 (not b0))) (let ((.def_22 (or b2 .def_21 .def_20))) (let ((.def_23 (* (/ 346394810802361 4503599627370496) r3))) (let ((.def_24 (* (- (/ 1088573802005915 9007199254740992)) r2))) (let ((.def_25 (* (- (/ 5944557997603297 2251799813685248)) r1))) (let ((.def_26 (* (- (/ 3237785834592927 2251799813685248)) r0))) (let ((.def_27 (+ .def_26 .def_25 .def_24 .def_23))) (let ((.def_28 (<= .def_27 (- (/ 3290748721519409 2251799813685248))))) (let ((.def_29 (not b3))) (let ((.def_30 (or .def_29 .def_21 .def_28))) (let ((.def_31 (* (- (/ 984697324864473 562949953421312)) r3))) (let ((.def_32 (* (/ 8496322043486171 9007199254740992) r2))) (let ((.def_33 (* (/ 238352539221577 562949953421312) r1))) (let ((.def_34 (* (/ 4661008423687171 4503599627370496) r0))) (let ((.def_35 (+ .def_34 .def_33 .def_32 .def_31))) (let ((.def_36 (<= .def_35 (/ 4039743455182629 4503599627370496)))) (let ((.def_37 (or b1 .def_29 .def_36))) (let ((.def_38 (* (/ 6019310751310153 9007199254740992) r3))) (let ((.def_39 (* (/ 2784336371499001 9007199254740992) r2))) (let ((.def_40 (* (- (/ 4097169356710929 9007199254740992)) r1))) (let ((.def_41 (* (- (/ 3857307260103893 4503599627370496)) r0))) (let ((.def_42 (+ .def_41 .def_40 .def_39 .def_38))) (let ((.def_43 (<= .def_42 (/ 1607418344945909 9007199254740992)))) (let ((.def_44 (or b1 b2 .def_43))) (let ((.def_45 (* (- (/ 4043035218930017 9007199254740992)) r3))) (let ((.def_46 (* (/ 530740044105499 1125899906842624) r2))) (let ((.def_47 (* (- (/ 699353232868657 1125899906842624)) r1))) (let ((.def_48 (* (/ 451193608381641 2251799813685248) r0))) (let ((.def_49 (+ .def_48 .def_47 .def_46 .def_45))) (let ((.def_50 (<= .def_49 (/ 424512493017583 9007199254740992)))) (let ((.def_51 (not b1))) (let ((.def_52 (or b3 .def_51 .def_50))) (let ((.def_53 (* (- (/ 4557212502818555 9007199254740992)) r3))) (let ((.def_54 (* (- (/ 2365921311204007 2251799813685248)) r2))) (let ((.def_55 (* (/ 1412253962412383 2251799813685248) r1))) (let ((.def_56 (* (- (/ 1421385190932745 2251799813685248)) r0))) (let ((.def_57 (+ .def_56 .def_55 .def_54 .def_53))) (let ((.def_58 (<= .def_57 (- (/ 2539064382431321 4503599627370496))))) (let ((.def_59 (or b2 .def_21 .def_58))) (let ((.def_60 (* (/ 2492741139951507 4503599627370496) r3))) (let ((.def_61 (* (- (/ 4498103831957149 9007199254740992)) r2))) (let ((.def_62 (* (/ 4486224211251949 4503599627370496) r1))) (let ((.def_63 (* (- (/ 2749203927109081 4503599627370496)) r0))) (let ((.def_64 (+ .def_63 .def_62 .def_61 .def_60))) (let ((.def_65 (<= .def_64 (/ 2544080902618291 4503599627370496)))) (let ((.def_66 (or .def_21 b3 .def_65))) (let ((.def_67 (* (- (/ 6830991932554921 9007199254740992)) r3))) (let ((.def_68 (* (- (/ 8918026924171123 9007199254740992)) r2))) (let ((.def_69 (* (- (/ 2673209961371847 9007199254740992)) r1))) (let ((.def_70 (* (- (/ 3385466989048879 4503599627370496)) r0))) (let ((.def_71 (+ .def_70 .def_69 .def_68 .def_67))) (let ((.def_72 (<= .def_71 (- (/ 2284308593568499 2251799813685248))))) (let ((.def_73 (or b0 .def_51 .def_72))) (let ((.def_74 (* (- (/ 315155814752767 9007199254740992)) r3))) (let ((.def_75 (* (/ 1520005557830121 2251799813685248) r2))) (let ((.def_76 (* (- (/ 1533097546401 281474976710656)) r1))) (let ((.def_77 (* (- (/ 2695827445915609 1125899906842624)) r0))) (let ((.def_78 (+ .def_77 .def_76 .def_75 .def_74))) (let ((.def_79 (<= .def_78 (- (/ 305889115545071 9007199254740992))))) (let ((.def_80 (or b2 .def_51 .def_79))) (let ((.def_81 (and .def_80 .def_73 .def_66 .def_59 .def_52 .def_44 .def_37 .def_30 .def_22 .def_14 .def_7))) .def_81)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)
