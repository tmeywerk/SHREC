(set-logic QF_LRA)
(declare-fun r0 () Real)
(declare-fun r1 () Real)
(declare-fun r2 () Real)
(declare-fun b1 () Bool)
(declare-fun b3 () Bool)
(declare-fun r3 () Real)
(declare-fun b0 () Bool)
(assert (let ((.def_0 (* (/ 6095087008973933 9007199254740992) r3))) (let ((.def_1 (* (/ 4482096316306507 4503599627370496) r2))) (let ((.def_2 (* (/ 39272346211761 562949953421312) r1))) (let ((.def_3 (* (- (/ 1403272942904163 4503599627370496)) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (/ 2276674003784315 2251799813685248)))) (let ((.def_6 (* (/ 1795439705429317 9007199254740992) r3))) (let ((.def_7 (* (/ 2423131442309727 2251799813685248) r2))) (let ((.def_8 (* (- (/ 1614613614047977 1125899906842624)) r1))) (let ((.def_9 (* (/ 1168976018015659 2251799813685248) r0))) (let ((.def_10 (+ .def_9 .def_8 .def_7 .def_6))) (let ((.def_11 (<= .def_10 (/ 405784774423417 4503599627370496)))) (let ((.def_12 (not b1))) (let ((.def_13 (or .def_12 .def_11 .def_5))) (let ((.def_14 (* (- (/ 865642906014751 562949953421312)) r3))) (let ((.def_15 (* (- (/ 3288645869113917 9007199254740992)) r2))) (let ((.def_16 (* (/ 1573817862121725 562949953421312) r1))) (let ((.def_17 (* (- (/ 1235311904235779 4503599627370496)) r0))) (let ((.def_18 (+ .def_17 .def_16 .def_15 .def_14))) (let ((.def_19 (<= .def_18 (/ 3257945992363437 9007199254740992)))) (let ((.def_20 (* (- (/ 2550384227469035 2251799813685248)) r3))) (let ((.def_21 (* (/ 4214478553222255 2251799813685248) r2))) (let ((.def_22 (* (- (/ 5462221820531375 9007199254740992)) r1))) (let ((.def_23 (* (/ 2876783015774267 2251799813685248) r0))) (let ((.def_24 (+ .def_23 .def_22 .def_21 .def_20))) (let ((.def_25 (<= .def_24 (/ 3511102781001891 4503599627370496)))) (let ((.def_26 (or b1 .def_25 .def_19))) (let ((.def_27 (* (/ 304930703290843 562949953421312) r3))) (let ((.def_28 (* (- (/ 4930088482016355 9007199254740992)) r2))) (let ((.def_29 (* (/ 4462714145009867 4503599627370496) r1))) (let ((.def_30 (* (- (/ 2707674451269189 1125899906842624)) r0))) (let ((.def_31 (+ .def_30 .def_29 .def_28 .def_27))) (let ((.def_32 (<= .def_31 (/ 285868860584237 9007199254740992)))) (let ((.def_33 (* (- (/ 2480329600207985 2251799813685248)) r3))) (let ((.def_34 (* (/ 3877047967819785 2251799813685248) r2))) (let ((.def_35 (* (- (/ 7767791555697029 9007199254740992)) r1))) (let ((.def_36 (* (- (/ 1760138195670379 1125899906842624)) r0))) (let ((.def_37 (+ .def_36 .def_35 .def_34 .def_33))) (let ((.def_38 (<= .def_37 (- (/ 2332705649353185 2251799813685248))))) (let ((.def_39 (or b3 .def_38 .def_32))) (let ((.def_40 (* (- (/ 269592375661901 281474976710656)) r3))) (let ((.def_41 (* (- (/ 2966575341001953 2251799813685248)) r2))) (let ((.def_42 (* (/ 412721975651023 2251799813685248) r1))) (let ((.def_43 (* (- (/ 6875085663504981 9007199254740992)) r0))) (let ((.def_44 (+ .def_43 .def_42 .def_41 .def_40))) (let ((.def_45 (<= .def_44 (- (/ 1614844734871605 1125899906842624))))) (let ((.def_46 (* (/ 5475329387271653 4503599627370496) r3))) (let ((.def_47 (* (- (/ 1983180395395951 2251799813685248)) r2))) (let ((.def_48 (* (/ 432025721082131 4503599627370496) r1))) (let ((.def_49 (* (- (/ 2191570500555387 9007199254740992)) r0))) (let ((.def_50 (+ .def_49 .def_48 .def_47 .def_46))) (let ((.def_51 (<= .def_50 (- (/ 419040187176155 4503599627370496))))) (let ((.def_52 (not b3))) (let ((.def_53 (or .def_52 .def_51 .def_45))) (let ((.def_54 (* (- (/ 4244489487473255 4503599627370496)) r3))) (let ((.def_55 (* (/ 7354375810050465 9007199254740992) r2))) (let ((.def_56 (* (- (/ 110476505079103 140737488355328)) r1))) (let ((.def_57 (* (/ 4532996408842791 9007199254740992) r0))) (let ((.def_58 (+ .def_57 .def_56 .def_55 .def_54))) (let ((.def_59 (<= .def_58 (- (/ 122582806756693 9007199254740992))))) (let ((.def_60 (* (- (/ 6467237745569377 9007199254740992)) r3))) (let ((.def_61 (* (- (/ 4635066156375323 2251799813685248)) r2))) (let ((.def_62 (* (/ 6755032852263977 2251799813685248) r1))) (let ((.def_63 (* (/ 5416463866966491 4503599627370496) r0))) (let ((.def_64 (+ .def_63 .def_62 .def_61 .def_60))) (let ((.def_65 (<= .def_64 (/ 2933536362874823 9007199254740992)))) (let ((.def_66 (not b0))) (let ((.def_67 (or .def_66 .def_65 .def_59))) (let ((.def_68 (* (/ 1977145481520037 1125899906842624) r3))) (let ((.def_69 (* (- (/ 607107315168045 281474976710656)) r2))) (let ((.def_70 (* (- (/ 849164808575357 9007199254740992)) r1))) (let ((.def_71 (* (- (/ 508272475360879 1125899906842624)) r0))) (let ((.def_72 (+ .def_71 .def_70 .def_69 .def_68))) (let ((.def_73 (<= .def_72 (/ 1793292113200439 4503599627370496)))) (let ((.def_74 (* (/ 4670180284674607 2251799813685248) r3))) (let ((.def_75 (* (- (/ 5213550890515639 4503599627370496)) r2))) (let ((.def_76 (* (- (/ 2493509237107309 2251799813685248)) r1))) (let ((.def_77 (* (- (/ 49227994409117 281474976710656)) r0))) (let ((.def_78 (+ .def_77 .def_76 .def_75 .def_74))) (let ((.def_79 (<= .def_78 (- (/ 1587923567836823 4503599627370496))))) (let ((.def_80 (or .def_52 .def_79 .def_73))) (let ((.def_81 (* (- (/ 4644139586246605 9007199254740992)) r3))) (let ((.def_82 (* (- (/ 3483700400435407 4503599627370496)) r2))) (let ((.def_83 (* (- (/ 742538105593791 9007199254740992)) r1))) (let ((.def_84 (* (- (/ 777082583015477 9007199254740992)) r0))) (let ((.def_85 (+ .def_84 .def_83 .def_82 .def_81))) (let ((.def_86 (<= .def_85 (- (/ 2139993389669645 4503599627370496))))) (let ((.def_87 (* (- (/ 5008878441886689 9007199254740992)) r3))) (let ((.def_88 (* (/ 836908299358555 4503599627370496) r2))) (let ((.def_89 (* (- (/ 4038660149816861 9007199254740992)) r1))) (let ((.def_90 (* (- (/ 330879234261559 562949953421312)) r0))) (let ((.def_91 (+ .def_90 .def_89 .def_88 .def_87))) (let ((.def_92 (<= .def_91 (- (/ 3358141770123077 4503599627370496))))) (let ((.def_93 (or .def_52 .def_92 .def_86))) (let ((.def_94 (and .def_93 .def_80 .def_67 .def_53 .def_39 .def_26 .def_13))) .def_94))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)
