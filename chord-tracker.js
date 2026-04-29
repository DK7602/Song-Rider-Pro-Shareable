/* Song Rider Pro - conservative piano chord tracker engine
   Browser mic audio -> stable simple chord labels for songwriting use.
   Exposes window.SongRiderChordTracker.create()
*/
(function(){
  'use strict';

  const ROOTS = ["C","C#","D","D#","E","F","F#","G","G#","A","A#","B"];
  const ALLOWED = new Set(["C","D","E","F","G","A","B","Cm","C#m","Dm","D#m","Em","Fm","F#m","Gm","G#m","Am","A#m","Bm"]);
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
    if(rest === 'maj' || rest === 'M') rest = '';
    return root + rest;
  }

  function create(){
    const state = {
      frames: [],
      candidateKey: '',
      candidateSince: 0,
      candidateCount: 0,
      locked: null,
      lockedAt: 0,
      lastResult: null,
      noiseFloor: 0.0035,
      lastDebug: null
    };

    const cfg = {
      minFreq: 55,
      maxFreq: 1500,
      keepMs: 1250,
      minDb: -96,
      maxPeaks: 84,
      silenceRmsFloor: 0.0055,
      chordStableMs: 780,
      noteStableMs: 360,
      chordMinConfidence: 0.60,
      noteMinConfidence: 0.55
    };

    function reset(){
      state.frames = [];
      state.candidateKey = '';
      state.candidateSince = 0;
      state.candidateCount = 0;
      state.locked = null;
      state.lockedAt = 0;
      state.lastResult = null;
      state.lastDebug = null;
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

    function detectSinglePitch(buf, sampleRate, level){
      if(!buf || !buf.length || !sampleRate || level < cfg.silenceRmsFloor) return null;
      const n = Math.min(buf.length, 4096);
      const minLag = Math.max(2, Math.floor(sampleRate / 1100));
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
      if(bestLag <= 0 || bestCorr < 0.46) return null;
      const freq = sampleRate / bestLag;
      const midi = freqToMidi(freq);
      const pc = ((Math.round(midi) % 12) + 12) % 12;
      return { pc, note: ROOTS[pc], confidence: clamp01(bestCorr * Math.min(1, level / 0.035)) };
    }

    function pickSpectralPeaks(data, sampleRate, fftSize){
      const binHz = sampleRate / fftSize;
      const peaks = [];
      let maxDb = -Infinity;
      for(let i=2;i<data.length-2;i++){
        const db = data[i];
        if(Number.isFinite(db) && db > maxDb) maxDb = db;
      }
      if(!Number.isFinite(maxDb) || maxDb < -82) return [];
      const floor = Math.max(cfg.minDb, maxDb - 48);
      for(let i=2;i<data.length-2;i++){
        const db = data[i];
        if(!Number.isFinite(db) || db < floor) continue;
        const freq = i * binHz;
        if(freq < cfg.minFreq || freq > cfg.maxFreq) continue;
        if(db < data[i-1] || db < data[i+1]) continue;
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

      const hasLowerSupport = (freq) => {
        for(const div of [2,3,4]){
          const f0 = freq / div;
          if(f0 < cfg.minFreq) continue;
          const tol = Math.max(6, f0 * 0.030);
          if(peaks.some(p => Math.abs(p.freq - f0) <= tol && p.amp >= topAmp * 0.018)) return true;
        }
        return false;
      };

      for(const pk of peaks){
        const midi = freqToMidi(pk.freq);
        const note = Math.round(midi);
        const cents = Math.abs((midi - note) * 100);
        if(cents > 34) continue;
        const pc = ((note % 12) + 12) % 12;
        const ampNorm = Math.max(0, pk.amp / topAmp);
        let w = Math.pow(ampNorm, 0.68) * (1 - cents / 48);

        // Piano overtones are bright. If a peak looks like an upper partial,
        // reduce its direct vote so harmonics do not become fake chord tones.
        if(hasLowerSupport(pk.freq)) w *= 0.18;
        if(pk.freq > 650) w *= 0.48;
        if(pk.freq > 1050) w *= 0.30;
        if(pk.freq >= 75 && pk.freq <= 560) w *= 1.35;
        if(pk.freq < 260) bass[pc] += w;
        chroma[pc] += w;
      }

      const max = Math.max(...chroma);
      if(max <= 0) return null;
      for(let i=0;i<12;i++){
        chroma[i] = chroma[i] / max;
        if(chroma[i] < 0.10) chroma[i] = 0;
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
      let cFrames = 0, rmsSum = 0;
      for(const fr of frames){
        rmsSum += Number(fr.level) || 0;
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
        for(let i=0;i<12;i++) chroma[i] += 0.055 * (pitchVotes[i] / pvMax);
      }
      const max = Math.max(...chroma);
      if(max <= 0) return null;
      for(let i=0;i<12;i++) chroma[i] /= max;
      const strongNotes = chroma.map((v,i)=>({pc:i,v})).filter(x => x.v >= 0.34).sort((a,b)=>b.v-a.v);
      const pitchPc = pvMax > 0 ? pitchVotes.indexOf(pvMax) : null;
      return { chroma, bass, frameCount: frames.length, strongNotes, pitchPc, pitchConfidence: pvMax / Math.max(1, frames.length), avgLevel: rmsSum / frames.length };
    }

    function templateCandidates(agg){
      const chroma = agg.chroma;
      const bass = agg.bass || Array(12).fill(0);
      const v = (pc) => Number(chroma[((pc % 12) + 12) % 12]) || 0;
      const b = (pc) => Number(bass[((pc % 12) + 12) % 12]) || 0;
      const templates = [
        { suffix:'',  pcs:[0,4,7], type:'maj' },
        { suffix:'m', pcs:[0,3,7], type:'min' }
      ];
      const out = [];
      for(let root=0; root<12; root++){
        for(const tpl of templates){
          const label = ROOTS[root] + tpl.suffix;
          if(!ALLOWED.has(label)) continue;
          const pcs = tpl.pcs.map(x => (root + x) % 12);
          const rootE = v(root), fifth = v(root+7);
          const maj3 = v(root+4), min3 = v(root+3);
          const need = pcs.reduce((s,pc)=>s + v(pc),0) / pcs.length;
          const outside = chroma.reduce((s,x,pc)=>s + (pcs.includes(pc) ? 0 : Math.max(0,x)),0) / 12;
          const weakest = Math.min(...pcs.map(pc => v(pc)));
          let score = need * 0.76 + rootE * 0.24 + fifth * 0.10 + b(root) * 0.13 - outside * 0.46;
          if(tpl.type === 'maj') score += (maj3 - min3) * 0.48;
          if(tpl.type === 'min') score += (min3 - maj3) * 0.54;
          if(agg.pitchPc === root) score += 0.035;
          out.push({ root, suffix:tpl.suffix, type:tpl.type, label, pcs, score, need, weakest, rootE, fifth, maj3, min3 });
        }
      }
      out.sort((a,b)=>b.score-a.score);
      return out;
    }

    function inferChord(agg){
      if(!agg || !Array.isArray(agg.chroma)) return null;
      const strongCount = agg.strongNotes.length;
      if(strongCount < 3) return null;
      const candidates = templateCandidates(agg);
      let best = candidates[0];
      if(!best) return null;
      const second = candidates[1] || null;

      // Phone/piano mics often make relative minors look stronger than the intended major
      // because they share two notes (G vs Em, C vs Am). If the best guess is a minor
      // and its relative major is close, prefer the major unless the minor root is truly dominant.
      if(best && best.suffix === 'm'){
        const relMajorRoot = (best.root + 3) % 12;
        const relMajor = candidates.find(c => c.root === relMajorRoot && c.suffix === '');
        if(relMajor && relMajor.score >= best.score - 0.18){
          const minorRootDominant = best.rootE >= 0.38;
          const minorThirdDominant = best.min3 >= best.maj3 * 1.22;
          const relMajorLooksValid = relMajor.maj3 >= 0.28 && relMajor.rootE >= 0.28;
          if(relMajorLooksValid && (!minorRootDominant || !minorThirdDominant)) best = relMajor;
        }
      }

      // Require all three chord tones. This is the main conservative upgrade:
      // no more writing a relative chord just because two shared notes are strong.
      if(best.weakest < 0.24) return null;

      const isMinor = best.suffix === 'm';
      const thirdOk = isMinor
        ? (best.min3 >= 0.27 && best.min3 >= best.maj3 * 1.05)
        : (best.maj3 >= 0.27 && best.maj3 >= best.min3 * 0.96);
      if(!thirdOk) return null;

      // If the top two chord guesses are too close, refuse to guess.
      if(second && second.score >= best.score - 0.075) return null;

      if(best.need < 0.39 || best.score < 0.38 || best.rootE < 0.22 || best.fifth < 0.20) return null;

      const margin = second ? Math.max(0, best.score - second.score) : 0.20;
      const confidence = clamp01((best.score * 0.52) + (best.need * 0.28) + (best.weakest * 0.22) + (margin * 1.05));
      if(confidence < cfg.chordMinConfidence) return null;
      return { type:'chord', value: cleanLabel(best.label), confidence, note: ROOTS[best.root], distinctStrong: strongCount, stable:false };
    }

    function inferNote(agg){
      if(!agg || !agg.strongNotes.length) return null;
      // Only output notes when it really looks like one note, not a partial chord.
      if(agg.strongNotes.length > 1) return null;
      const best = agg.strongNotes[0];
      const pitchPc = Number.isFinite(agg.pitchPc) ? agg.pitchPc : best.pc;
      if(best.v < 0.66 || agg.pitchConfidence < 0.36) return null;
      const value = pcName(pitchPc);
      const conf = clamp01(Math.max(best.v * 0.55, Number(agg.pitchConfidence) || 0));
      if(conf < cfg.noteMinConfidence) return null;
      return { type:'note', value, note:value, confidence: conf, distinctStrong: agg.strongNotes.length, stable:false };
    }

    function stabilize(det, nowMs){
      if(!det || !det.value){
        state.candidateKey = '';
        state.candidateSince = 0;
        state.candidateCount = 0;
        state.locked = null;
        return null;
      }
      const value = cleanLabel(det.value);
      const key = det.type + ':' + value;
      if(key === state.candidateKey){
        state.candidateCount += 1;
      }else{
        state.candidateKey = key;
        state.candidateSince = nowMs;
        state.candidateCount = 1;
      }
      const stableMs = nowMs - (Number(state.candidateSince) || nowMs);
      const neededMs = det.type === 'chord' ? cfg.chordStableMs : cfg.noteStableMs;
      const neededFrames = det.type === 'chord' ? 8 : 6;
      const sameLocked = state.locked && state.locked.type === det.type && state.locked.value === value;
      if(sameLocked || (stableMs >= neededMs && state.candidateCount >= neededFrames)){
        const locked = { ...det, value, note: cleanLabel(det.note || value), stable:true };
        state.locked = locked;
        state.lockedAt = nowMs;
        return locked;
      }
      return null;
    }

    function analyze(analyser, audioCtx, nowMs){
      const ctx = audioCtx || (analyser && analyser.context) || null;
      const sampleRate = ctx && ctx.sampleRate ? ctx.sampleRate : 48000;
      const t = Number(nowMs) || (typeof performance !== 'undefined' ? performance.now() : Date.now());
      const timeData = getTimeData(analyser);
      const level = rms(timeData);

      // Adaptive-ish noise gate. Keeps room noise and key clicks from becoming chords.
      if(level < cfg.silenceRmsFloor || level < Math.max(cfg.silenceRmsFloor, state.noiseFloor * 1.65)){
        state.noiseFloor = Math.max(0.0025, Math.min(0.010, state.noiseFloor * 0.96 + level * 0.04));
        reset();
        return null;
      }
      state.noiseFloor = Math.max(0.0025, Math.min(0.012, state.noiseFloor * 0.995 + level * 0.005));

      const freqData = getFreqData(analyser);
      if(!freqData) return null;
      const peaks = pickSpectralPeaks(freqData, sampleRate, analyser.fftSize || 8192);
      const chromaPack = buildChromaFromPeaks(peaks);
      const pitch = detectSinglePitch(timeData, sampleRate, level);

      if(chromaPack || pitch){
        pushFrame({
          chroma: chromaPack && chromaPack.chroma,
          bass: chromaPack && chromaPack.bass,
          pitchPc: pitch ? pitch.pc : null,
          pitchConfidence: pitch ? pitch.confidence : 0,
          level
        }, t);
      }

      const agg = aggregate();
      if(!agg || agg.frameCount < 4) return null;
      let det = inferChord(agg) || inferNote(agg);
      state.lastDebug = agg ? {
        level,
        notes: agg.chroma.map((v,i)=>ROOTS[i] + ':' + Number(v).toFixed(2)).join(' '),
        strong: agg.strongNotes.map(n=>ROOTS[n.pc]).join(','),
        det: det ? `${det.type}:${det.value}:${det.confidence.toFixed(2)}` : ''
      } : null;
      const stable = stabilize(det, t);
      state.lastResult = stable || det || null;
      return stable ? stable : (det ? { ...det, stable:false } : null);
    }

    function debug(){ return state.lastDebug; }

    return { analyze, reset, cleanLabel, debug };
  }

  window.SongRiderChordTracker = { create, cleanLabel };
})();
