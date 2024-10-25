import java.util.ArrayList;

public class JomoPipi {
  static final record CyclePos(int cycle_id, int pos) {
  }

  static final record Cycles(Integer[][] cycles, CyclePos[] position) {
  }

  static Cycles findCycle(int n) {
    CyclePos[] position = new CyclePos[n];
    ArrayList<Integer[]> cycles = new ArrayList<>();
    cycles.add(null);

    for (int i = 0; i < n; ++i) {
      if (position[i] != null) {
        continue;
      }

      ArrayList<Integer> cycle = new ArrayList<>();
      final int cycle_id = cycles.size();

      for (int j = i, pos = 0; position[j] == null; ++pos) {
        cycle.add(Integer.valueOf(j));
        position[j] = new CyclePos(cycle_id, pos);
        if (j % 2 == 0) {
          j = n - 1 - (j >> 1);
        } else {
          j = (j - 1) >> 1;
        }
      }

      cycles.add(cycle.toArray(new Integer[0]));
    }

    return new Cycles(cycles.toArray(new Integer[0][0]), position);
  }

  public static String stringFunc(String s, long x) {
    final Cycles cyc = findCycle(s.length());
    StringBuilder ret = new StringBuilder(s.length());
    for (int i = 0; i < s.length(); ++i) {
      final var cycle_pos = cyc.position[i];
      final var cycle = cyc.cycles[cycle_pos.cycle_id];
      ret.append(s.charAt(cycle[(int) ((x + cycle_pos.pos) % cycle.length)]));
    }
    return ret.toString();
  }
}