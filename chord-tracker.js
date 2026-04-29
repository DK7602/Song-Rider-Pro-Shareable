/* Song Rider Pro - dedicated chord tracker engine
   Purpose: browser mic audio -> stable simple chord labels for songwriting use.
   Exposes window.SongRiderChordTracker.create({ clamp })
*/
(function(){
  'use strict';

  const ROOTS = ["C","C#","D","D#","E","F","F#","G","G#","A","A#","B"];
  const clamp01 = (n) => Math.max(0, Math.min(1, Number(n) || 0));
  const freqToMidi = (f) => 69 + 12 * Math.log2(f / 440);
  const pcName = (pc) => ROOTS[((Math.round(pc) % 12) + 12) % 12];

  function cleanLabel(value){
    let out = String(value || '').trim();
    if(!out) return '';
    out = out.replace(/♯/g,'#').replace(/♭/g,'b').replace(/\s+/g,'');
    const m = out.match(/^([A-Ga-g])([#b]?)(.*)$/);
    if(!m) return out;
    const root = m[1].toUpperCase() + (m[2] || '');
    let rest = String(m[3] || '');
    rest = rest.replace(/^minor$/i,'m').replace(/^min$/i,'m').replace(/^-/,'m');
    // Keep the tracker practical: avoid noisy color-chord labels unless explicitly chosen.
    if(rest === 'maj' || rest === 'M') rest = '';
    return root + rest;
  }

  function create(opts){
    const state = {
      frames: [],
      candidateKey: '',
      candidateCount: 0,
      locked: null,
      lockedAt: 0,
      lastResult: null,
      lastStrongNotes: []
    };

    const cfg = {
      minFreq: 65,
      maxFreq: 1850,
      keepMs: 1050,
      minDb: -92,
      maxPeaks: 72,
      stableChordFrames: 3,
      stableNoteFrames: 4
    };

    function reset(){
      state.frames = [];
      state.candidateKey = '';
      state.candidateCount = 0;
      state.locked = null;
      state.lockedAt = 0;
      state.lastResult = null;
      state.lastStrongNotes = [];
    }

    function getFreqData(analyser){
      if(!analyser) return null;
      if(!state.freqBuf || state.freqBuf.length !== analyser.frequencyBinCount){
        state.freqBuf = new Float32Array(analyser.frequencyBinCount);
      }
      analyser.getFloatFrequencyData(state.freqBuf);
      return state.freqBuf;
    }

    function getTimeData(analyser){
      if(!analyser) return null;
      if(!state.timeBuf || state.timeBuf.length !== analyser.fftSize){
        state.timeBuf = new Float32Array(analyser.fftSize);
      }
      analyser.getFloatTimeDomainData(state.timeBuf);
      return state.timeBuf;
    }

    function rms(buf){
      if(!buf || !buf.length) return 0;
      let s = 0;
      for(let i=0;i<buf.length;i++) s += buf[i] * buf[i];
      return Math.sqrt(s / buf.length);
    }

    function detectSinglePitch(buf, sampleRate){
      if(!buf || !buf.length || !sampleRate) return null;
      const level = rms(buf);
      if(level < 0.003) return null;
      const n = Math.min(buf.length, 4096);
      const minLag = Math.max(2, Math.floor(sampleRate / 1200));
      const maxLag = Math.min(n - 2, Math.ceil(sampleRate / 65));
      let bestLag = -1, bestCorr = 0;
      for(let lag=minLag; lag<=maxLag; lag++){
        let sum = 0, aa = 0, bb = 0;
        const usable = n - lag;
        for(let i=0;i<usable;i++){
          const a = buf[i], b = buf[i+lag];
          sum += a*b; aa += a*a; bb += b*b;
        }
        const corr = sum / (Math.sqrt(aa*bb) || 1);
        if(corr > bestCorr){ bestCorr = corr; bestLag = lag; }
      }
      if(bestLag <= 0 || bestCorr < 0.38) return null;
      const freq = sampleRate / bestLag;
      const midi = freqToMidi(freq);
      const pc = ((Math.round(midi) % 12) + 12) % 12;
      return { pc, note: ROOTS[pc], confidence: clamp01(bestCorr * Math.min(1, level / 0.03)) };
    }

    function pickSpectralPeaks(data, sampleRate, fftSize){
      const binHz = sampleRate / fftSize;
      const peaks = [];
      let maxDb = -Infinity;
      for(let i=2;i<data.length-2;i++){
        const db = data[i];
        if(Number.isFinite(db) && db > maxDb) maxDb = db;
      }
      const floor = Math.max(cfg.minDb, maxDb - 54);
      for(let i=2;i<data.length-2;i++){
        const db = data[i];
        if(!Number.isFinite(db) || db < floor) continue;
        const freq = i * binHz;
        if(freq < cfg.minFreq || freq > cfg.maxFreq) continue;
        if(db < data[i-1] || db < data[i+1]) continue;
        // small parabola-ish local peak preference
        if(db < data[i-2] || db < data[i+2]) continue;
        const amp = Math.pow(10, db / 20);
        peaks.push({ freq, amp, db });
      }
      peaks.sort((a,b) => b.amp - a.amp);
      return peaks.slice(0, cfg.maxPeaks);
    }

    function buildChromaFromPeaks(peaks){
      const chroma = Array(12).fill(0);
      const bass = Array(12).fill(0);
      if(!peaks || !peaks.length) return null;
      const topAmp = peaks[0].amp || 1;

      const hasFundamentalSupport = (freq) => {
        for(const div of [2,3,4,5]){
          const f0 = freq / div;
          if(f0 < cfg.minFreq) continue;
          const tol = Math.max(5.5, f0 * 0.026);
          const found = peaks.find(p => Math.abs(p.freq - f0) <= tol && p.amp >= topAmp * 0.012);
          if(found) return true;
        }
        return false;
      };

      for(const pk of peaks){
        const midi = freqToMidi(pk.freq);
        const note = Math.round(midi);
        const cents = Math.abs((midi - note) * 100);
        if(cents > 38) continue;
        const pc = ((note % 12) + 12) % 12;
        const ampNorm = Math.max(0, pk.amp / topAmp);
        let w = Math.pow(ampNorm, 0.62) * (1 - cents / 55);

        // Piano chords produce bright harmonics. Down-weight likely upper harmonics.
        if(pk.freq > 700) w *= 0.52;
        if(pk.freq > 1200) w *= 0.34;
        if(hasFundamentalSupport(pk.freq)) w *= 0.26;

        // Favor lower-mid fundamentals where piano chord identity usually lives.
        if(pk.freq >= 80 && pk.freq <= 520) w *= 1.38;
        if(pk.freq < 260) bass[pc] += w;
        chroma[pc] += w;

        // Subharmonic vote: if an upper partial strongly implies a musical lower note,
        // add a small vote only when a nearby lower support exists.
        for(const div of [2,3]){
          const f0 = pk.freq / div;
          if(f0 < cfg.minFreq || f0 > 900) continue;
          const m0 = freqToMidi(f0);
          const n0 = Math.round(m0);
          const c0 = Math.abs((m0 - n0) * 100);
          if(c0 > 26) continue;
          const tol = Math.max(5.5, f0 * 0.026);
          const support = peaks.some(p => Math.abs(p.freq - f0) <= tol);
          if(!support) continue;
          const pc0 = ((n0 % 12) + 12) % 12;
          chroma[pc0] += w * (div === 2 ? 0.20 : 0.12);
        }
      }

      const max = Math.max(...chroma);
      if(max <= 0) return null;
      for(let i=0;i<12;i++){
        chroma[i] = chroma[i] / max;
        if(chroma[i] < 0.075) chroma[i] = 0;
      }
      const bassMax = Math.max(...bass);
      if(bassMax > 0){
        for(let i=0;i<12;i++) bass[i] = bass[i] / bassMax;
      }
      return { chroma, bass };
    }

    function pushFrame(frame, nowMs){
      state.frames.push({ ...frame, t: nowMs });
      const cutoff = nowMs - cfg.keepMs;
      while(state.frames.length && state.frames[0].t < cutoff) state.frames.shift();
    }

    function aggregate(){
      const frames = state.frames;
      if(!frames.length) return null;
      const chroma = Array(12).fill(0);
      const bass = Array(12).fill(0);
      const pitchVotes = Array(12).fill(0);
      let cFrames = 0;
      for(const fr of frames){
        if(Array.isArray(fr.chroma)){
          cFrames++;
          for(let i=0;i<12;i++) chroma[i] += Number(fr.chroma[i]) || 0;
        }
        if(Array.isArray(fr.bass)){
          for(let i=0;i<12;i++) bass[i] += Number(fr.bass[i]) || 0;
        }
        if(Number.isFinite(fr.pitchPc)){
          pitchVotes[fr.pitchPc] += Math.max(0.04, Number(fr.pitchConfidence) || 0.04);
        }
      }
      if(!cFrames) return null;
      for(let i=0;i<12;i++){
        chroma[i] /= cFrames;
        bass[i] /= cFrames;
      }
      const pvMax = Math.max(...pitchVotes);
      if(pvMax > 0){
        for(let i=0;i<12;i++) chroma[i] += 0.10 * (pitchVotes[i] / pvMax);
      }
      const max = Math.max(...chroma);
      if(max <= 0) return null;
      for(let i=0;i<12;i++) chroma[i] /= max;
      const strongNotes = chroma.map((v,i)=>({pc:i,v})).filter(x => x.v >= 0.32).sort((a,b)=>b.v-a.v);
      const pitchPc = pvMax > 0 ? pitchVotes.indexOf(pvMax) : null;
      return { chroma, bass, frameCount: frames.length, strongNotes, pitchPc, pitchConfidence: pvMax / Math.max(1, frames.length) };
    }

    function templateCandidates(agg){
      const chroma = agg.chroma;
      const bass = agg.bass || Array(12).fill(0);
      const v = (pc) => Number(chroma[((pc % 12) + 12) % 12]) || 0;
      const b = (pc) => Number(bass[((pc % 12) + 12) % 12]) || 0;
      const templates = [
        { suffix:'',  pcs:[0,4,7], type:'maj' },
        { suffix:'m', pcs:[0,3,7], type:'min' },
        { suffix:'7', pcs:[0,4,7,10], type:'dom7' },
        { suffix:'m7', pcs:[0,3,7,10], type:'min7' }
      ];
      const out = [];
      for(let root=0; root<12; root++){
        for(const tpl of templates){
          const pcs = tpl.pcs.map(x => (root + x) % 12);
          const rootE = v(root), fifth = v(root+7);
          const maj3 = v(root+4), min3 = v(root+3), flat7 = v(root+10);
          const need = pcs.reduce((s,pc)=>s + v(pc),0) / pcs.length;
          const outside = chroma.reduce((s,x,pc)=>s + (pcs.includes(pc) ? 0 : Math.max(0,x)),0) / 12;
          let score = need * 0.72 + rootE * 0.22 + fifth * 0.10 + b(root) * 0.12 - outside * 0.38;
          if(tpl.type === 'maj' || tpl.type === 'dom7') score += (maj3 - min3) * 0.42;
          if(tpl.type === 'min' || tpl.type === 'min7') score += (min3 - maj3) * 0.48;
          if(tpl.type === 'dom7' || tpl.type === 'min7'){
            score += flat7 >= 0.48 ? flat7 * 0.08 : -0.36;
          }
          if(agg.pitchPc === root) score += 0.04;
          out.push({ root, suffix:tpl.suffix, type:tpl.type, score, need, rootE, fifth, maj3, min3, flat7 });
        }
      }
      out.sort((a,b)=>b.score-a.score);
      return out;
    }


    function triadPcsForCandidate(cand){
      if(!cand) return [];
      const suffix = String(cand.suffix || '');
      if(suffix === '') return [cand.root % 12, (cand.root + 4) % 12, (cand.root + 7) % 12];
      if(suffix === 'm') return [cand.root % 12, (cand.root + 3) % 12, (cand.root + 7) % 12];
      return [];
    }

    function uniquePcBetween(aPcs, bPcs){
      const bSet = new Set(bPcs.map(x => ((x % 12) + 12) % 12));
      const uniq = aPcs.filter(pc => !bSet.has(((pc % 12) + 12) % 12));
      return uniq.length === 1 ? uniq[0] : null;
    }

    function correctSharedToneConfusion(best, candidates, agg){
      // Piano mic tracking often confuses triads that share two notes:
      // G (G-B-D) vs Em (E-G-B), and F (F-A-C) vs Am (A-C-E).
      // This does not prefer major or minor. It checks the note unique to each chord.
      if(!best || !agg || !Array.isArray(agg.chroma)) return best;
      const bestPcs = triadPcsForCandidate(best);
      if(bestPcs.length !== 3) return best;

      const v = (pc) => Number(agg.chroma[((pc % 12) + 12) % 12]) || 0;
      const bass = Array.isArray(agg.bass) ? agg.bass : Array(12).fill(0);
      const b = (pc) => Number(bass[((pc % 12) + 12) % 12]) || 0;

      let corrected = best;
      let bestCorrectionScore = -Infinity;

      for(const alt of candidates){
        if(!alt || alt === best) continue;
        if(alt.suffix !== '' && alt.suffix !== 'm') continue;
        const altPcs = triadPcsForCandidate(alt);
        if(altPcs.length !== 3) continue;
        const shared = bestPcs.filter(pc => altPcs.includes(pc)).length;
        if(shared !== 2) continue;

        const bestUnique = uniquePcBetween(bestPcs, altPcs);
        const altUnique = uniquePcBetween(altPcs, bestPcs);
        if(bestUnique == null || altUnique == null) continue;

        const bestUniqueE = v(bestUnique);
        const altUniqueE = v(altUnique);
        const bestRootSupport = Math.max(v(best.root), b(best.root));
        const altRootSupport = Math.max(v(alt.root), b(alt.root));

        const closeEnough = alt.score >= best.score - 0.18;
        const uniqueClearlyFavorsAlt = altUniqueE >= 0.26 && altUniqueE >= bestUniqueE + 0.10;
        const winnerUniqueWeak = bestUniqueE < 0.24;
        const rootDoesNotContradict = altRootSupport >= bestRootSupport - 0.18;
        const correctionScore = (altUniqueE - bestUniqueE) + (alt.score - best.score) * 0.35 + (altRootSupport - bestRootSupport) * 0.18;

        if(closeEnough && uniqueClearlyFavorsAlt && winnerUniqueWeak && rootDoesNotContradict && correctionScore > bestCorrectionScore){
          corrected = alt;
          bestCorrectionScore = correctionScore;
        }
      }

      return corrected;
    }

    function inferChord(agg){
      if(!agg || !Array.isArray(agg.chroma)) return null;
      const strongCount = agg.strongNotes.length;
      const candidates = templateCandidates(agg);
      let best = candidates[0];
      if(!best) return null;

      // Prefer plain triad over 7th unless the 7 is clearly strong.
      if(best.suffix === '7' || best.suffix === 'm7'){
        const triadSuffix = best.suffix === 'm7' ? 'm' : '';
        const triad = candidates.find(c => c.root === best.root && c.suffix === triadSuffix);
        if(triad && (best.flat7 < 0.58 || triad.score >= best.score - 0.11)) best = triad;
      }

      best = correctSharedToneConfusion(best, candidates, agg);

      const isMinor = best.suffix.startsWith('m');
      const thirdOk = isMinor
        ? (best.min3 >= 0.20 && best.min3 >= best.maj3 * 0.90)
        : (best.maj3 >= 0.20 && best.maj3 >= best.min3 * 0.84);
      const enough = strongCount >= 2 ? 0.285 : 0.60;
      if(best.need < enough || best.score < 0.26 || !thirdOk) return null;

      let suffix = best.suffix;
      if(suffix === '7' && best.flat7 < 0.62) suffix = '';
      if(suffix === 'm7' && best.flat7 < 0.62) suffix = 'm';

      const confidence = clamp01((best.score + best.need + best.rootE + (strongCount >= 3 ? 0.20 : 0)) / 2.18);
      return { type:'chord', value: cleanLabel(ROOTS[best.root] + suffix), confidence, note: ROOTS[best.root], distinctStrong: strongCount };
    }

    function inferNote(agg){
      if(!agg || !agg.strongNotes.length) return null;
      const best = agg.strongNotes[0];
      const pitchPc = Number.isFinite(agg.pitchPc) ? agg.pitchPc : best.pc;
      const value = pcName(pitchPc);
      const conf = clamp01(Math.max(best.v * 0.42, Number(agg.pitchConfidence) || 0));
      return { type:'note', value, note:value, confidence: conf, distinctStrong: agg.strongNotes.length };
    }

    function stabilize(det, nowMs){
      if(!det || !det.value){
        if(state.locked && nowMs - state.lockedAt < 650) return state.locked;
        return null;
      }
      const key = det.type + ':' + cleanLabel(det.value);
      if(key === state.candidateKey) state.candidateCount += 1;
      else { state.candidateKey = key; state.candidateCount = 1; }

      const needed = det.type === 'chord' ? cfg.stableChordFrames : cfg.stableNoteFrames;
      const confident = det.confidence >= (det.type === 'chord' ? 0.50 : 0.46);
      const sameLocked = state.locked && state.locked.type === det.type && state.locked.value === det.value;
      if(sameLocked || state.candidateCount >= needed || confident){
        const locked = { ...det, value: cleanLabel(det.value), note: cleanLabel(det.note || det.value) };
        state.locked = locked;
        state.lockedAt = nowMs;
        return locked;
      }
      if(state.locked && nowMs - state.lockedAt < 420) return state.locked;
      return null;
    }

    function analyze(analyser, audioCtx, nowMs){
      const ctx = audioCtx || (analyser && analyser.context) || null;
      const sampleRate = ctx && ctx.sampleRate ? ctx.sampleRate : 48000;
      const t = Number(nowMs) || (typeof performance !== 'undefined' ? performance.now() : Date.now());
      const freqData = getFreqData(analyser);
      if(!freqData) return null;
      const peaks = pickSpectralPeaks(freqData, sampleRate, analyser.fftSize || 8192);
      const chromaPack = buildChromaFromPeaks(peaks);
      const timeData = getTimeData(analyser);
      const pitch = detectSinglePitch(timeData, sampleRate);

      if(chromaPack || pitch){
        pushFrame({
          chroma: chromaPack && chromaPack.chroma,
          bass: chromaPack && chromaPack.bass,
          pitchPc: pitch ? pitch.pc : null,
          pitchConfidence: pitch ? pitch.confidence : 0
        }, t);
      }

      const agg = aggregate();
      if(!agg || agg.frameCount < 2) return stabilize(null, t);
      let det = inferChord(agg);
      if(!det || det.confidence < 0.26){
        det = inferNote(agg);
      }
      const stable = stabilize(det, t);
      state.lastResult = stable || det || null;
      return stable;
    }

    return { analyze, reset, cleanLabel };
  }

  window.SongRiderChordTracker = { create, cleanLabel };
})();
