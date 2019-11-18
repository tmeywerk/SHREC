(set-logic QF_LRA)
(declare-fun b0 () Bool)
(declare-fun b1 () Bool)
(declare-fun r0 () Real)
(declare-fun b3 () Bool)
(declare-fun r1 () Real)
(declare-fun r2 () Real)
(declare-fun r3 () Real)
(assert (let ((.def_0 (* (/ 2257006664950089 4503599627370496) r3))) (let ((.def_1 (* (- (/ 402353950605899 562949953421312)) r2))) (let ((.def_2 (* (/ 5192081921494607 9007199254740992) r1))) (let ((.def_3 (* (- (/ 3763179969342373 2251799813685248)) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (- (/ 748745822113233 1125899906842624))))) (let ((.def_6 (* (- (/ 3067329638119589 2251799813685248)) r3))) (let ((.def_7 (* (/ 6580513884560019 9007199254740992) r2))) (let ((.def_8 (* (- (/ 8833700298155377 9007199254740992)) r1))) (let ((.def_9 (* (/ 1684018302496369 9007199254740992) r0))) (let ((.def_10 (+ .def_9 .def_8 .def_7 .def_6))) (let ((.def_11 (<= .def_10 (- (/ 4379582999252679 4503599627370496))))) (let ((.def_12 (not b3))) (let ((.def_13 (or .def_12 .def_11 .def_5))) (let ((.def_14 (* (- (/ 1556465696818535 1125899906842624)) r3))) (let ((.def_15 (* (- (/ 3682967413560323 4503599627370496)) r2))) (let ((.def_16 (* (/ 2846596934080399 2251799813685248) r1))) (let ((.def_17 (* (/ 433409562214475 562949953421312) r0))) (let ((.def_18 (+ .def_17 .def_16 .def_15 .def_14))) (let ((.def_19 (<= .def_18 (- (/ 348514977816805 4503599627370496))))) (let ((.def_20 (* (- (/ 4252755611471003 2251799813685248)) r3))) (let ((.def_21 (* (- (/ 7002381294991055 9007199254740992)) r2))) (let ((.def_22 (* (/ 2752425712894809 9007199254740992) r1))) (let ((.def_23 (* (- (/ 2320601569589687 2251799813685248)) r0))) (let ((.def_24 (+ .def_23 .def_22 .def_21 .def_20))) (let ((.def_25 (<= .def_24 (- (/ 4272412628067945 2251799813685248))))) (let ((.def_26 (not b1))) (let ((.def_27 (or .def_26 .def_25 .def_19))) (let ((.def_28 (* (/ 6692803141683431 9007199254740992) r3))) (let ((.def_29 (* (- (/ 1962821824865405 2251799813685248)) r2))) (let ((.def_30 (* (/ 1853726747730621 2251799813685248) r1))) (let ((.def_31 (* (/ 1757350568395809 4503599627370496) r0))) (let ((.def_32 (+ .def_31 .def_30 .def_29 .def_28))) (let ((.def_33 (<= .def_32 (/ 1424864058822789 4503599627370496)))) (let ((.def_34 (* (- (/ 1084455331033765 2251799813685248)) r3))) (let ((.def_35 (* (/ 2919633582249619 2251799813685248) r2))) (let ((.def_36 (* (- (/ 4773171637392123 9007199254740992)) r1))) (let ((.def_37 (* (- (/ 5908161941598013 9007199254740992)) r0))) (let ((.def_38 (+ .def_37 .def_36 .def_35 .def_34))) (let ((.def_39 (<= .def_38 (- (/ 1197540400341193 9007199254740992))))) (let ((.def_40 (or .def_26 .def_39 .def_33))) (let ((.def_41 (* (- (/ 1084873541642225 2251799813685248)) r3))) (let ((.def_42 (* (- (/ 3281973062690481 9007199254740992)) r2))) (let ((.def_43 (* (- (/ 10994124287957 281474976710656)) r1))) (let ((.def_44 (* (/ 1406722309412039 1125899906842624) r0))) (let ((.def_45 (+ .def_44 .def_43 .def_42 .def_41))) (let ((.def_46 (<= .def_45 (/ 2214939024973295 9007199254740992)))) (let ((.def_47 (* (- (/ 3987035949091859 9007199254740992)) r3))) (let ((.def_48 (* (- (/ 7322384649385613 9007199254740992)) r2))) (let ((.def_49 (* (- (/ 519088082617547 4503599627370496)) r1))) (let ((.def_50 (* (- (/ 4838605510806181 9007199254740992)) r0))) (let ((.def_51 (+ .def_50 .def_49 .def_48 .def_47))) (let ((.def_52 (<= .def_51 (- (/ 2474793341319921 2251799813685248))))) (let ((.def_53 (or b3 .def_52 .def_46))) (let ((.def_54 (* (/ 1561479228584173 9007199254740992) r3))) (let ((.def_55 (* (- (/ 3707641825913963 2251799813685248)) r2))) (let ((.def_56 (* (/ 1793622333249287 1125899906842624) r1))) (let ((.def_57 (* (/ 2559650489952717 9007199254740992) r0))) (let ((.def_58 (+ .def_57 .def_56 .def_55 .def_54))) (let ((.def_59 (<= .def_58 (/ 3796507780269491 4503599627370496)))) (let ((.def_60 (* (/ 6363343245238133 4503599627370496) r3))) (let ((.def_61 (* (- (/ 304564052025893 140737488355328)) r2))) (let ((.def_62 (* (/ 144555229563547 4503599627370496) r1))) (let ((.def_63 (* (/ 1206647837154707 2251799813685248) r0))) (let ((.def_64 (+ .def_63 .def_62 .def_61 .def_60))) (let ((.def_65 (<= .def_64 (- (/ 3063560022087071 9007199254740992))))) (let ((.def_66 (or b0 .def_65 .def_59))) (let ((.def_67 (* (/ 303378729683915 281474976710656) r3))) (let ((.def_68 (* (- (/ 7597432357749423 4503599627370496)) r2))) (let ((.def_69 (* (- (/ 1625785264872397 1125899906842624)) r1))) (let ((.def_70 (* (/ 2916576416130893 2251799813685248) r0))) (let ((.def_71 (+ .def_70 .def_69 .def_68 .def_67))) (let ((.def_72 (<= .def_71 (- (/ 301317551013147 4503599627370496))))) (let ((.def_73 (* (/ 50432323306205 1125899906842624) r3))) (let ((.def_74 (* (/ 1201368883249235 2251799813685248) r2))) (let ((.def_75 (* (- (/ 6911881093758137 4503599627370496)) r1))) (let ((.def_76 (* (- (/ 3183620441748177 2251799813685248)) r0))) (let ((.def_77 (+ .def_76 .def_75 .def_74 .def_73))) (let ((.def_78 (<= .def_77 (- (/ 1461199658928929 1125899906842624))))) (let ((.def_79 (or .def_26 .def_78 .def_72))) (let ((.def_80 (and .def_79 .def_66 .def_53 .def_40 .def_27 .def_13))) .def_80))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)