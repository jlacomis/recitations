public class Shifty {
	public static void main(String[] args) {
		int a = 0x10101010;
		int b = a << 5;
		int c = a << 32;
		int d = a << -1;
		int result = a + b + c + d;
		System.out.println(result);
	}
}
