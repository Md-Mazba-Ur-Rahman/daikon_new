// Elements of array are objects of a class Student.
public class Tiny {

    int inc(int x) {
        return x + 1;
    }

    public static void main (String[] args) {
        Tiny t = new Tiny();

        for (int i = 0; i < 5; i++) {
            t.inc(i);
        }
    }
}
