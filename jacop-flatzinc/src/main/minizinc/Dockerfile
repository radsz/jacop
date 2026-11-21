#------------------------------------------------------------------------------#
# This file contains the setup for building a JaCoP image for the MiniZinc
# challenges. It uses multi-stage builds in order to keep the images small.
#
# Build it from the repository root so the current sources are used:
#   docker build -f jacop-flatzinc/src/main/minizinc/Dockerfile -t jacop-mznc .
#
# MZNC_IMAGE selects the MiniZinc challenge base image.
#------------------------------------------------------------------------------#

ARG MZNC_IMAGE=minizinc/mznc2025:latest

# Build JaCoP with Java 25.

FROM maven:3.9-eclipse-temurin-25 AS build

WORKDIR /jacop
COPY . .

RUN mvn -B -Pall -DskipTests -Dspotless.skip=true package \
  && mkdir -p /dist/lib /dist/mzn-lib \
  && cp "$(ls jacop-all/target/jacop-all-*.jar | grep -v -e sources -e javadoc)" /dist/jacop.jar \
  && cp -r jacop-all/target/lib/. /dist/lib/ \
  && cp -r jacop-flatzinc/src/main/minizinc/org/jacop/minizinc/. /dist/mzn-lib/ \
  && cp -r jacop-all/src/main/aot-training /dist/aot-training

# Native image of the FlatZinc front end: it starts in milliseconds and runs compiled code at once,
# where the JVM needs 0.1-0.5 s before JaCoP runs at speed. Oracle GraalVM (GraalVM Free Terms and
# Conditions, free to use and redistribute without a fee) compiles it with profile-guided
# optimization from the training models, so long runs are as fast as on the JVM or faster
# (osolpro benchmarks/native-startup). The build stage's fzn-jacop-native-build does it; x86-64-v3 is
# any x86 CPU since about 2015.

FROM maven:3.9-eclipse-temurin-25 AS native

ARG GRAALVM_URL=https://download.oracle.com/graalvm/25/latest/graalvm-jdk-25_linux-x64_bin.tar.gz
RUN apt-get update && apt-get install -y --no-install-recommends gcc libc6-dev zlib1g-dev \
  && rm -rf /var/lib/apt/lists/* \
  && mkdir -p /opt/graalvm && curl -fsSL "$GRAALVM_URL" | tar xz -C /opt/graalvm --strip-components=1
COPY --from=build /jacop/jacop-all/target/fzn-jacop-native-build /native/
COPY --from=build /jacop/jacop-all/target/lib /native/lib
COPY --from=build /jacop/jacop-all/src/main/aot-training /native/aot-training
COPY --from=build /dist/jacop.jar /native/
RUN cd /native && ln -s jacop.jar "$(grep -o 'jacop-all-[^"]*\.jar' fzn-jacop-native-build)" \
  && GRAALVM_HOME=/opt/graalvm bash ./fzn-jacop-native-build

# Java 25 runtime, for JACOP_JVM=1 (fzn-exec then runs the JVM with its ahead-of-time cache).

FROM eclipse-temurin:25-jre AS jre

# The challenge image.

FROM ${MZNC_IMAGE}

ENV JAVA_HOME=/opt/java/openjdk
ENV PATH="${JAVA_HOME}/bin:${PATH}"

COPY --from=jre /opt/java/openjdk /opt/java/openjdk
COPY --from=build /dist/jacop.jar /jacop/jacop.jar
COPY --from=build /dist/lib /jacop/lib
COPY --from=build /dist/mzn-lib/ /entry_data/mzn-lib/
COPY --from=native /native/fzn-jacop-native /jacop/fzn-jacop-native

# The JVM's ahead-of-time cache (Java 25): one training JVM solves the training models with their
# own search, free search and LCG free search, and records the classes and method profiles they use.
# fzn-exec starts from it, which saves about 0.2 s of start-up on every run (osolpro
# benchmarks/jvm-startup); the Challenge compares times in whole seconds, so on easy instances that
# is often a full second. The cache is made with the runtime JVM of this image and the classpath of
# fzn-exec, or the JVM rejects it. JVM warnings (such as a rejected cache) go to stderr, never into
# the FlatZinc output on stdout.
# -XX:+UseTransparentHugePages backs the heap with 2 MB pages where the host kernel allows it
# (madvise or always), about 5 % less solving time on the same search (osolpro
# benchmarks/narrow-types); on a host without them the JVM runs as before.
# The training models are mounted from the build stage, so they never become part of the image.
RUN --mount=type=bind,from=build,source=/dist/aot-training,target=/aot-training \
    java -Xmx2G -Xss100M -XX:AOTCacheOutput=/jacop/jacop.aot -cp "/jacop/jacop.jar:/jacop/lib/*" \
      org.jacop.fz.AotTraining --models /aot-training > /dev/null \
  && rm -f /jacop/jacop.aot.config \
  && chmod a+r /jacop/jacop.aot \
  && printf '%s\n' \
    '#!/bin/bash' \
    'if [ -z "$JACOP_JVM" ]; then exec /jacop/fzn-jacop-native -Xmx10G -cs "$@"; fi' \
    'exec java -server -Xmx10G -Xss100M -XX:+UseTransparentHugePages -XX:AOTCache=/jacop/jacop.aot \' \
    '  -Xlog:disable -Xlog:all=warning:stderr \' \
    '  -cp "/jacop/jacop.jar:/jacop/lib/*" org.jacop.fz.Fz2jacop -cs "$@"' \
    > /entry_data/fzn-exec \
  && chmod a+x /entry_data/fzn-exec

# Run as a regular user; it gets the challenge solver configuration from root's home.
RUN useradd --create-home --shell /bin/bash jacop \
  && cp -r /root/.minizinc /home/jacop/.minizinc \
  && chown -R jacop:jacop /home/jacop/.minizinc

USER jacop
