(set-logic QF_LRA)
(declare-fun b1 () Bool)
(declare-fun b2 () Bool)
(declare-fun r0 () Real)
(declare-fun r1 () Real)
(declare-fun r2 () Real)
(declare-fun r3 () Real)
(declare-fun b0 () Bool)
(declare-fun b3 () Bool)
(assert (let ((.def_0 (* (- (/ 2793253783561229 9007199254740992)) r3))) (let ((.def_1 (* (/ 16022279086819 562949953421312) r2))) (let ((.def_2 (* (/ 255422461671351 9007199254740992) r1))) (let ((.def_3 (* (- (/ 1322840116544895 2251799813685248)) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (- (/ 1509659306524557 4503599627370496))))) (let ((.def_6 (not b1))) (let ((.def_7 (or b0 .def_6 .def_5))) (let ((.def_8 (* (- (/ 2286751780930455 9007199254740992)) r3))) (let ((.def_9 (* (- (/ 4687764562098613 9007199254740992)) r2))) (let ((.def_10 (* (/ 246883449146791 1125899906842624) r1))) (let ((.def_11 (* (/ 2790622077368025 2251799813685248) r0))) (let ((.def_12 (+ .def_11 .def_10 .def_9 .def_8))) (let ((.def_13 (<= .def_12 (/ 1040149078403869 2251799813685248)))) (let ((.def_14 (or b2 b3 .def_13))) (let ((.def_15 (* (- (/ 4988660922599823 4503599627370496)) r3))) (let ((.def_16 (* (- (/ 5681338128747897 9007199254740992)) r2))) (let ((.def_17 (* (/ 507461603847249 9007199254740992) r1))) (let ((.def_18 (* (/ 2584588280860819 2251799813685248) r0))) (let ((.def_19 (+ .def_18 .def_17 .def_16 .def_15))) (let ((.def_20 (<= .def_19 (/ 806784180672073 4503599627370496)))) (let ((.def_21 (or b2 b1 .def_20))) (let ((.def_22 (* (- (/ 1814122025730707 2251799813685248)) r3))) (let ((.def_23 (* (/ 5992584546507535 9007199254740992) r2))) (let ((.def_24 (* (/ 273754870071331 1125899906842624) r1))) (let ((.def_25 (* (- (/ 428497156878037 4503599627370496)) r0))) (let ((.def_26 (+ .def_25 .def_24 .def_23 .def_22))) (let ((.def_27 (<= .def_26 (/ 45201730667779 281474976710656)))) (let ((.def_28 (or .def_6 b2 .def_27))) (let ((.def_29 (* (- (/ 564916853582387 1125899906842624)) r3))) (let ((.def_30 (* (/ 8573739120065705 4503599627370496) r2))) (let ((.def_31 (* (- (/ 80949485317035 70368744177664)) r1))) (let ((.def_32 (* (- (/ 1771581129690653 562949953421312)) r0))) (let ((.def_33 (+ .def_32 .def_31 .def_30 .def_29))) (let ((.def_34 (<= .def_33 (- (/ 3931905717810003 9007199254740992))))) (let ((.def_35 (or b1 b2 .def_34))) (let ((.def_36 (* (- (/ 263017155614193 4503599627370496)) r3))) (let ((.def_37 (* (/ 717412783461411 1125899906842624) r2))) (let ((.def_38 (* (- (/ 195481157259737 562949953421312)) r1))) (let ((.def_39 (* (/ 2479989112619113 4503599627370496) r0))) (let ((.def_40 (+ .def_39 .def_38 .def_37 .def_36))) (let ((.def_41 (<= .def_40 (/ 6021874984409171 9007199254740992)))) (let ((.def_42 (not b2))) (let ((.def_43 (not b3))) (let ((.def_44 (or .def_43 .def_42 .def_41))) (let ((.def_45 (* (- (/ 3677548407254921 9007199254740992)) r3))) (let ((.def_46 (* (/ 1758122241507003 4503599627370496) r2))) (let ((.def_47 (* (/ 939236433277353 9007199254740992) r1))) (let ((.def_48 (* (/ 3496784403787655 9007199254740992) r0))) (let ((.def_49 (+ .def_48 .def_47 .def_46 .def_45))) (let ((.def_50 (<= .def_49 (/ 2070176567275611 4503599627370496)))) (let ((.def_51 (or .def_43 .def_6 .def_50))) (let ((.def_52 (* (/ 2687206237371839 2251799813685248) r3))) (let ((.def_53 (* (/ 1491433163355035 4503599627370496) r2))) (let ((.def_54 (* (/ 2436126327452097 4503599627370496) r1))) (let ((.def_55 (* (- (/ 355057875809463 281474976710656)) r0))) (let ((.def_56 (+ .def_55 .def_54 .def_53 .def_52))) (let ((.def_57 (<= .def_56 (/ 4258214164930903 4503599627370496)))) (let ((.def_58 (or b1 .def_43 .def_57))) (let ((.def_59 (* (- (/ 1234584020622967 4503599627370496)) r3))) (let ((.def_60 (* (- (/ 352399175404263 562949953421312)) r2))) (let ((.def_61 (* (/ 2992030691707891 9007199254740992) r1))) (let ((.def_62 (* (- (/ 88956646394403 562949953421312)) r0))) (let ((.def_63 (+ .def_62 .def_61 .def_60 .def_59))) (let ((.def_64 (<= .def_63 (- (/ 1269752989772243 9007199254740992))))) (let ((.def_65 (or b2 .def_6 .def_64))) (let ((.def_66 (* (/ 925089693738521 4503599627370496) r3))) (let ((.def_67 (* (- (/ 622787666079201 1125899906842624)) r2))) (let ((.def_68 (* (- (/ 737198457234073 1125899906842624)) r1))) (let ((.def_69 (* (/ 317722870040087 9007199254740992) r0))) (let ((.def_70 (+ .def_69 .def_68 .def_67 .def_66))) (let ((.def_71 (<= .def_70 (- (/ 898942493866681 4503599627370496))))) (let ((.def_72 (or b1 b0 .def_71))) (let ((.def_73 (* (/ 180641624040695 562949953421312) r3))) (let ((.def_74 (* (- (/ 2044619565691945 2251799813685248)) r2))) (let ((.def_75 (* (/ 4559049528794773 9007199254740992) r1))) (let ((.def_76 (* (/ 6991779482768261 9007199254740992) r0))) (let ((.def_77 (+ .def_76 .def_75 .def_74 .def_73))) (let ((.def_78 (<= .def_77 (/ 6271359769965179 9007199254740992)))) (let ((.def_79 (or .def_43 .def_42 .def_78))) (let ((.def_80 (* (/ 210093155848923 2251799813685248) r3))) (let ((.def_81 (* (/ 4119397647231887 9007199254740992) r2))) (let ((.def_82 (* (- (/ 3484416277320687 2251799813685248)) r1))) (let ((.def_83 (* (/ 461303263332829 562949953421312) r0))) (let ((.def_84 (+ .def_83 .def_82 .def_81 .def_80))) (let ((.def_85 (<= .def_84 (/ 4360337137301629 9007199254740992)))) (let ((.def_86 (not b0))) (let ((.def_87 (or b2 .def_86 .def_85))) (let ((.def_88 (* (- (/ 8755525230880485 9007199254740992)) r3))) (let ((.def_89 (* (/ 2223119306119669 4503599627370496) r2))) (let ((.def_90 (* (- (/ 736558440824577 562949953421312)) r1))) (let ((.def_91 (* (- (/ 1591603090233747 4503599627370496)) r0))) (let ((.def_92 (+ .def_91 .def_90 .def_89 .def_88))) (let ((.def_93 (<= .def_92 (- (/ 2389451205549831 4503599627370496))))) (let ((.def_94 (or b3 .def_6 .def_93))) (let ((.def_95 (and .def_94 .def_87 .def_79 .def_72 .def_65 .def_58 .def_51 .def_44 .def_35 .def_28 .def_21 .def_14 .def_7))) .def_95)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)