package ch.brucker.projects.holtestgen.examples.unit.List;
import java.util.Collections;
import java.util.List;
import java.math.BigInteger;

public class JavaList
{
    public static List<BigInteger> sort (List<BigInteger> l){
        Collections.sort(l);
        return l;
    }
}
