#
# This ProGuard configuration file illustrates how to process Scala
# applications, including the Scala runtime.
# Usage:
#     java -jar proguard.jar @scala.pro
#

# Specify the input jars, output jars, and library jars.

-injars 'core/target/scala-2.9.2/picasso:-core-components_2.9.2-0.2.jar'
# -injars frontend/basic/target/scala-2.9.2/picasso:-basic-frontend_2.9.2-0.1.jar
-injars core/lib/org.sat4j.core-2.3.1.jar(!META-INF/**)
-injars core/lib/org.sat4j.maxsat-2.3.1.jar(!META-INF/**)
-injars core/lib/org.sat4j.pb-2.3.1.jar(!META-INF/**)
-injars <user.home>/.ivy2/cache/org.apache.commons/commons-lang3/jars/commons-lang3-3.1.jar(!META-INF/**)
-injars <user.home>/.sbt/boot/scala-2.9.2/lib/scala-library.jar(!META-INF/**)
#-injars <user.home>/.sbt/boot/scala-2.9.2/lib/scala-compiler.jar(!META-INF/**)

-outjars picasso-core.jar

-libraryjars <java.home>/lib/rt.jar
#-libraryjars /usr/lib/jvm/java-6-openjdk-amd64/jre/lib/rt.jar

# Ignore some sat4j dependencies

-dontwarn org.apache.commons.cli.**

# Ignore some compiler artefacts.
-dontwarn **$$anonfun$*
-dontwarn scala.collection.immutable.RedBlack$Empty
-dontwarn ap.parser.CollectingVisitor$KeepArg

# Ignore some dependencies on the Scala compiler library, under the assumption
# that it is not used.

-dontwarn scala.tools.**,plugintemplate.**

# Save the obfuscation mapping to a file, so you can de-obfuscate any stack
# traces later on. Keep a fixed source file attribute and all line number
# tables to get line numbers in the stack traces.
# You can comment this out if you're not interested in stack traces.

#-printmapping out.map
#-renamesourcefileattribute SourceFile
#-keepattributes SourceFile,LineNumberTable

# Preserve all annotations.
-keepattributes *Annotation*

# You can print out the seeds that are matching the keep options below.
#-printseeds out.seeds

# Preserve all public applications.

-keepclasseswithmembers public class * {
    public static void main(java.lang.String[]);
}

# Preserve some classes and class members that are accessed by means of
# introspection.

-keep class * implements org.xml.sax.EntityResolver

-keepclassmembers class * {
    ** MODULE$;
}

-keepclassmembernames class scala.concurrent.forkjoin.ForkJoinPool {
    long eventCount;
    int  workerCounts;
    int  runControl;
    scala.concurrent.forkjoin.ForkJoinPool$WaitQueueNode syncStack;
    scala.concurrent.forkjoin.ForkJoinPool$WaitQueueNode spareStack;
}

-keepclassmembernames class scala.concurrent.forkjoin.ForkJoinWorkerThread {
    int base;
    int sp;
    int runState;
}

-keepclassmembernames class scala.concurrent.forkjoin.ForkJoinTask {
    int status;
}

-keepclassmembernames class scala.concurrent.forkjoin.LinkedTransferQueue {
    scala.concurrent.forkjoin.LinkedTransferQueue$PaddedAtomicReference head;
    scala.concurrent.forkjoin.LinkedTransferQueue$PaddedAtomicReference tail;
    scala.concurrent.forkjoin.LinkedTransferQueue$PaddedAtomicReference cleanMe;
}

# Preserve some classes and class members that are accessed by means of
# introspection in the Scala compiler library, if it is processed as well.

#-keep class * implements jline.Completor
#-keep class * implements jline.Terminal

#-keep class scala.tools.nsc.Global

#-keepclasseswithmembers class * {
#    <init>(scala.tools.nsc.Global);
#}

#-keepclassmembers class * {
#    *** scala_repl_value();
#    *** scala_repl_result();
#}

# Preserve all native method names and the names of their classes.

-keepclasseswithmembernames class * {
    native <methods>;
}

# Preserve the special static methods that are required in all enumeration
# classes.

-keepclassmembers class * extends java.lang.Enum {
    public static **[] values();
    public static ** valueOf(java.lang.String);
}

# Explicitly preserve all serialization members. The Serializable interface
# is only a marker interface, so it wouldn't save them.
# You can comment this out if your application doesn't use serialization.
# If your code contains serializable classes that have to be backward 
# compatible, please refer to the manual.

-keepclassmembers class * implements java.io.Serializable {
    static final long serialVersionUID;
    static final java.io.ObjectStreamField[] serialPersistentFields;
    private void writeObject(java.io.ObjectOutputStream);
    private void readObject(java.io.ObjectInputStream);
    java.lang.Object writeReplace();
    java.lang.Object readResolve();
}

# Your application may contain more items that need to be preserved; 
# typically classes that are dynamically created using Class.forName:

# -keep public class mypackage.MyClass
# -keep public interface mypackage.MyInterface
# -keep public class * implements mypackage.MyInterface

# optimisatio
-dontoptimize
-dontobfuscate
