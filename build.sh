#!/bin/bash
set echo on
cd src
zip -q -r ../dist/geronimo-forgunte-mail.jar org/
cd ../bin/
zip -q -r ../dist/geronimo-forgunte-mail.jar org/
cd ../dist/

cp geronimo-forgunte-mail.jar ../../MailProxy/WEB-INF/lib/
cp geronimo-forgunte-mail.jar ../../MailProxy/libs/geronimo-forgunte-mail.jar
