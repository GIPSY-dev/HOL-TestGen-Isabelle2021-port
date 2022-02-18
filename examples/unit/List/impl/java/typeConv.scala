import ch.brucker.projects.holtestgen.examples.unit.List.JavaList
import scala.collection.JavaConverters._
import java.math.BigInteger
import java.util.ArrayList;

object myList {
  def sort[T] (l:List[BigInt]) = {    
    	val javaList           = l.map(_.bigInteger).asJava           
        val modifiableJavaList = new ArrayList[BigInteger](javaList)  
        val sortedJavaList     = JavaList.sort(modifiableJavaList)
        val sortedScalaList    = sortedJavaList.asScala.map(new BigInt(_)).foldRight (List[BigInt]()) (_ :: _)
    	sortedScalaList
  }	
} /* object myList */
