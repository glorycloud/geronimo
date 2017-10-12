/**
 * Licensed to the Apache Software Foundation (ASF) under one or more
 * contributor license agreements.  See the NOTICE file distributed with
 * this work for additional information regarding copyright ownership.
 * The ASF licenses this file to You under the Apache License, Version 2.0
 * (the "License"); you may not use this file except in compliance with
 * the License.  You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */


package org.apache.geronimo.javamail.store.nntp;

import javax.mail.Session;
import javax.mail.URLName;

/**
 * NNTP implementation of javax.mail.Store over an SSL connection.
 *
 * @version $Rev: 673152 $ $Date: 2008-07-02 01:37:38 +0800 (周三, 02 七月 2008) $
 */
public class NNTPSSLStore extends NNTPStore {
    /**
     * Construct an NNTPSSLStore item.
     *
     * @param session The owning javamail Session.
     * @param urlName The Store urlName, which can contain server target information.
     */
	public NNTPSSLStore(Session session, URLName urlName) {
        // we're the imaps protocol, our default connection port is 563, and we must use
        // an SSL connection for the initial hookup 
		super(session, urlName, "nntps", DEFAULT_NNTP_SSL_PORT, true);
	}
}



