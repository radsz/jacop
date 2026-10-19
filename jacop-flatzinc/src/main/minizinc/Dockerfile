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
  && cp -r jacop-flatzinc/src/main/minizinc/org/jacop/minizinc/. /dist/mzn-lib/

# Java 25 runtime.

FROM eclipse-temurin:25-jre AS jre

# The challenge image.

FROM ${MZNC_IMAGE}

ENV JAVA_HOME=/opt/java/openjdk
ENV PATH="${JAVA_HOME}/bin:${PATH}"

COPY --from=jre /opt/java/openjdk /opt/java/openjdk
COPY --from=build /dist/jacop.jar /jacop/jacop.jar
COPY --from=build /dist/lib /jacop/lib
COPY --from=build /dist/mzn-lib/ /entry_data/mzn-lib/

RUN printf '%s\n' \
    '#!/bin/bash' \
    'exec java -server -Xmx10G -Xss100M -cp "/jacop/jacop.jar:/jacop/lib/*" org.jacop.fz.Fz2jacop -cs "$@"' \
    > /entry_data/fzn-exec \
  && chmod a+x /entry_data/fzn-exec
