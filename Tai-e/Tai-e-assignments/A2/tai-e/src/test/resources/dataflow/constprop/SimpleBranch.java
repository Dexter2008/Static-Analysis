class SimpleBranch {

//    static void NAC(int p) {
//        int x;
//        if (p > 0) {
//            x = 1;
//        } else {
//            x = 2;
//        }
//        int y = x;
//    }
void undefined1(boolean b) {
    int x, undef;
    if (b) {
        x = undef;
    } else {
        x = 10;
    }
    int y = x;
}

    void undefined2(boolean b) {
        int undef;
        int x = undef;
        x = 20;
        int a = x;
    }
//    void whileConstant() {
//        int a, b = 1, c = 1;
//        int i = 0;
//        while (i < 10) {
//            a = b;
//            b = c;
//            c = 1;
//            ++i;
//        }
//    }

//    void whileNAC() {
//        int a, b = 0, c = 0;
//        int i = 0;
//        while (i < 10) {
//            a = b;
//            b = c;
//            c = 1;
//            ++i;
//        }
//    }
//
//    void whileUndefinedConstant() {
//        int a, b, c;
//        int i = 0;
//        while (i < 10) {
//            a = b;
//            b = c;
//            c = 1;
//            ++i;
//        }
    }
}
